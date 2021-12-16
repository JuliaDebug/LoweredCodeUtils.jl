using LoweredCodeUtils
using LoweredCodeUtils.JuliaInterpreter
using LoweredCodeUtils: callee_matches, istypedef, exclude_named_typedefs
using JuliaInterpreter: is_global_ref, is_quotenode
using Test

function hastrackedexpr(stmt; heads=LoweredCodeUtils.trackedheads)
    haseval = false
    if isa(stmt, Expr)
        if stmt.head === :call
            f = stmt.args[1]
            haseval = f === :eval || (callee_matches(f, Base, :getproperty) && is_quotenode(stmt.args[2], :eval))
            callee_matches(f, Core, :_typebody!) && return true, haseval
            callee_matches(f, Core, :_setsuper!) && return true, haseval
            f === :include && return true, haseval
        elseif stmt.head === :thunk
            any(s->any(hastrackedexpr(s; heads=heads)), stmt.args[1].code) && return true, haseval
        elseif stmt.head ∈ heads
            return true, haseval
        end
    end
    return false, haseval
end

function minimal_evaluation(predicate, src::Core.CodeInfo, edges::CodeEdges; kwargs...)
    isrequired = fill(false, length(src.code))
    for (i, stmt) in enumerate(src.code)
        if !isrequired[i]
            isrequired[i], haseval = predicate(stmt)
            if haseval
                isrequired[edges.succs[i]] .= true
            end
        end
    end
    # All tracked expressions are marked. Now add their dependencies.
    lines_required!(isrequired, src, edges; kwargs...)
    return isrequired
end

function allmissing(mod::Module, names)
    for name in names
        isdefined(mod, name) && return false
    end
    return true
end

module ModEval
end

module ModSelective
end

@testset "CodeEdges" begin
    ex = quote
        x = 1
        y = x+1
        a = sin(0.3)
        z = x^2 + y
        k = rand()
        b = 2*a + 5
    end
    frame = Frame(ModSelective, ex)
    src = frame.framecode.src
    edges = CodeEdges(src)
    # Check that the result of direct evaluation agrees with selective evaluation
    Core.eval(ModEval, ex)
    isrequired = lines_required(:x, src, edges)
    @test sum(isrequired) == 1
    selective_eval_fromstart!(frame, isrequired)
    @test ModSelective.x === ModEval.x
    @test allmissing(ModSelective, (:y, :z, :a, :b, :k))
    @test !allmissing(ModSelective, (:x, :y))    # add :y here to test the `all` part of the test itself
    # To evaluate z we need to do all the computations for y
    isrequired = lines_required(:z, src, edges)
    selective_eval_fromstart!(frame, isrequired)
    @test ModSelective.y === ModEval.y
    @test ModSelective.z === ModEval.z
    @test allmissing(ModSelective, (:a, :b, :k))    # ... but not a and b
    isrequired = lines_required(length(src.code)-1, src, edges)  # this should be the assignment of b
    selective_eval_fromstart!(frame, isrequired)
    @test ModSelective.a === ModEval.a
    @test ModSelective.b === ModEval.b
    # Test that we get two separate evaluations of k
    @test allmissing(ModSelective, (:k,))
    isrequired = lines_required(:k, src, edges)
    selective_eval_fromstart!(frame, isrequired)
    @test ModSelective.k != ModEval.k

    # Control-flow
    ex = quote
        flag2 = true
        z2 = 15
        if flag2
            x2 = 5
            a2 = 1
        else
            y2 = 7
            a2 = 2
        end
    end
    frame = Frame(ModSelective, ex)
    src = frame.framecode.src
    edges = CodeEdges(src)
    isrequired = lines_required(:a2, src, edges)
    selective_eval_fromstart!(frame, isrequired)
    Core.eval(ModEval, ex)
    @test ModSelective.a2 === ModEval.a2 == 1
    @test allmissing(ModSelective, (:z2, :x2, :y2))
    # Now do it for the other branch, to make sure it's really sound.
    # Also switch up the order of the assignments inside each branch.
    ex = quote
        flag3 = false
        z3 = 15
        if flag3
            a3 = 1
            x3 = 5
        else
            a3 = 2
            y3 = 7
        end
    end
    frame = Frame(ModSelective, ex)
    src = frame.framecode.src
    edges = CodeEdges(src)
    isrequired = lines_required(:a3, src, edges)
    selective_eval_fromstart!(frame, isrequired)
    Core.eval(ModEval, ex)
    @test ModSelective.a3 === ModEval.a3 == 2
    @test allmissing(ModSelective, (:z3, :x3, :y3))

    # Capturing dependencies of an `@eval` statement
    interpT = Expr(:$, :T)   # $T that won't get parsed during file-loading
    ex = quote
        foo() = 0
        for T in (Float32, Float64)
            @eval feval1(::$interpT) = 1
        end
        bar() = 1
    end
    Core.eval(ModEval, ex)
    @test ModEval.foo() == 0
    @test ModEval.bar() == 1
    frame = Frame(ModSelective, ex)
    src = frame.framecode.src
    edges = CodeEdges(src)
    # Mark just the load of Core.eval
    haseval(stmt) = (isa(stmt, Expr) && JuliaInterpreter.hasarg(isequal(:eval), stmt.args)) ||
                    (isa(stmt, Expr) && stmt.head === :call && is_quotenode(stmt.args[1], Core.eval))
    isrequired = map(haseval, src.code)
    @test sum(isrequired) == 1
    isrequired[edges.succs[findfirst(isrequired)]] .= true   # add lines that use Core.eval
    lines_required!(isrequired, src, edges)
    selective_eval_fromstart!(frame, isrequired)
    @test ModSelective.feval1(1.0f0) == 1
    @test ModSelective.feval1(1.0)   == 1
    @test_throws MethodError ModSelective.feval1(1)
    @test_throws UndefVarError ModSelective.foo()
    @test_throws UndefVarError ModSelective.bar()
    # Run test from the docs
    # Lowered code isn't very suitable to jldoctest (it can vary with each Julia version),
    # so better to run it here
    ex = quote
        s11 = 0
        k11 = 5
        for i = 1:3
            global s11, k11
            s11 += rand(1:5)
            k11 += i
        end
    end
    frame = Frame(ModSelective, ex)
    JuliaInterpreter.finish_and_return!(frame, true)
    @test ModSelective.k11 == 11
    @test 3 <= ModSelective.s11 <= 15
    Core.eval(ModSelective, :(k11 = 0; s11 = -1))
    edges = CodeEdges(frame.framecode.src)
    isrequired = lines_required(:s11, frame.framecode.src, edges)
    selective_eval_fromstart!(frame, isrequired, true)
    @test ModSelective.k11 == 0
    @test 3 <= ModSelective.s11 <= 15

    # Control-flow in an abstract type definition
    ex = :(abstract type StructParent{T, N} <: AbstractArray{T, N} end)
    frame = Frame(ModSelective, ex)
    src = frame.framecode.src
    edges = CodeEdges(src)
    # Check that the StructParent name is discovered everywhere it is used
    var = edges.byname[:StructParent]
    isrequired = minimal_evaluation(hastrackedexpr, src, edges)
    selective_eval_fromstart!(frame, isrequired, true)
    @test supertype(ModSelective.StructParent) === AbstractArray
    # Also check redefinition (it's OK when the definition doesn't change)
    Core.eval(ModEval, ex)
    frame = Frame(ModEval, ex)
    src = frame.framecode.src
    edges = CodeEdges(src)
    isrequired = minimal_evaluation(hastrackedexpr, src, edges)
    selective_eval_fromstart!(frame, isrequired, true)
    @test supertype(ModEval.StructParent) === AbstractArray

    # Finding all dependencies in a struct definition
    # Nonparametric
    ex = :(struct NoParam end)
    frame = Frame(ModSelective, ex)
    src = frame.framecode.src
    edges = CodeEdges(src)
    isrequired = minimal_evaluation(stmt->(LoweredCodeUtils.ismethod3(stmt)&&stmt.args[1]===:NoParam,false), src, edges)  # initially mark only the constructor
    selective_eval_fromstart!(frame, isrequired, true)
    @test isa(ModSelective.NoParam(), ModSelective.NoParam)
    # Parametric
    ex = quote
        struct Struct{T} <: StructParent{T,1}
            x::Vector{T}
        end
    end
    frame = Frame(ModSelective, ex)
    src = frame.framecode.src
    edges = CodeEdges(src)
    isrequired = minimal_evaluation(stmt->(LoweredCodeUtils.ismethod3(stmt)&&stmt.args[1]===:Struct,false), src, edges)  # initially mark only the constructor
    selective_eval_fromstart!(frame, isrequired, true)
    @test isa(ModSelective.Struct([1,2,3]), ModSelective.Struct{Int})
    # Keyword constructor (this generates :copyast expressions)
    ex = quote
        struct KWStruct
            x::Int
            y::Float32
            z::String
            function KWStruct(; x::Int=1, y::Float32=1.0f0, z::String="hello")
                return new(x, y, z)
            end
        end
    end
    frame = Frame(ModSelective, ex)
    src = frame.framecode.src
    edges = CodeEdges(src)
    isrequired = minimal_evaluation(stmt->(LoweredCodeUtils.ismethod3(stmt),false), src, edges)  # initially mark only the constructor
    selective_eval_fromstart!(frame, isrequired, true)
    kws = ModSelective.KWStruct(y=5.0f0)
    @test kws.y === 5.0f0

    # Anonymous functions
    ex = :(max_values(T::Union{map(X -> Type{X}, Base.BitIntegerSmall_types)...}) = 1 << (8*sizeof(T)))
    frame = Frame(ModSelective, ex)
    src = frame.framecode.src
    edges = CodeEdges(src)
    isrequired = fill(false, length(src.code))
    @assert Meta.isexpr(src.code[end-1], :method, 3)
    isrequired[end-1] = true
    lines_required!(isrequired, src, edges)
    selective_eval_fromstart!(frame, isrequired, true)
    @test ModSelective.max_values(Int16) === 65536

    # Avoid redefining types
    ex = quote
        struct MyNewType
            x::Int

            MyNewType(y::Int) = new(y)
        end
    end
    Core.eval(ModEval, ex)
    frame = Frame(ModEval, ex)
    src = frame.framecode.src
    edges = CodeEdges(src)
    isrequired = minimal_evaluation(stmt->(LoweredCodeUtils.ismethod3(stmt),false), src, edges; norequire=exclude_named_typedefs(src, edges))  # initially mark only the constructor
    bbs = Core.Compiler.compute_basic_blocks(src.code)
    for (iblock, block) in enumerate(bbs.blocks)
        r = LoweredCodeUtils.rng(block)
        if iblock == length(bbs.blocks)
            @test any(idx->isrequired[idx], r)
        else
            @test !any(idx->isrequired[idx], r)
        end
    end

    # https://github.com/timholy/Revise.jl/issues/538
    thk = Meta.lower(ModEval, quote
        try
            global function v1(x::Float32)
                println("F32")
            end
        catch e
            println("caught error")
        end
    end)
    src = thk.args[1]
    edges = CodeEdges(src)
    lr = lines_required(:v1, src, edges)
    idx = findfirst(stmt->Meta.isexpr(stmt, :leave), src.code)
    @test lr[idx]

    # https://github.com/timholy/Revise.jl/issues/599
    thk = Meta.lower(Main, quote
        mutable struct A
            x::Int

            A(x) = new(f(x))
            f(x) = x^2
        end
    end)
    src = thk.args[1]
    edges = CodeEdges(src)
    idx = findfirst(stmt->Meta.isexpr(stmt, :method), src.code)
    lr = lines_required(idx, src, edges; norequire=exclude_named_typedefs(src, edges))
    idx = findfirst(stmt->Meta.isexpr(stmt, :(=)) && Meta.isexpr(stmt.args[2], :call) && is_global_ref(stmt.args[2].args[1], Core, :Box), src.code)
    @test lr[idx]
    # but make sure we don't break primitivetype & abstracttype (https://github.com/timholy/Revise.jl/pull/611)
    if isdefined(Core, :_primitivetype)
        thk = Meta.lower(Main, quote
            primitive type WindowsRawSocket sizeof(Ptr) * 8 end
        end)
        src = thk.args[1]
        edges = CodeEdges(src)
        idx = findfirst(istypedef, src.code)
        r = LoweredCodeUtils.typedef_range(src, idx)
        @test last(r) == length(src.code) - 1
    end

    @testset "Display" begin
        # worth testing because this has proven quite crucial for debugging and
        # ensuring that these structures are as "self-documenting" as possible.
        io = IOBuffer()
        l = LoweredCodeUtils.Links(Int[], [3, 5], LoweredCodeUtils.NamedVar[:hello])
        show(io, l)
        str = String(take!(io))
        @test occursin('∅', str)
        @test !occursin("GlobalRef", str)
        # CodeLinks
        ex = quote
            s = 0.0
            for i = 1:5
                global s
                s += rand()
            end
            return s
        end
        lwr = Meta.lower(Main, ex)
        src = lwr.args[1]
        cl = LoweredCodeUtils.CodeLinks(src)
        show(io, cl)
        str = String(take!(io))
        @test occursin(r"slot 1:\n  preds: ssas: \[\d+, \d+\], slots: ∅, names: ∅;\n  succs: ssas: \[\d+, \d+, \d+\], slots: ∅, names: ∅;\n  assign @: \[\d+, \d+\]", str)
        @test occursin(r"succs: ssas: ∅, slots: \[\d+\], names: ∅;", str)
        @test occursin(r"s:\n  preds: ssas: \[\d+\], slots: ∅, names: ∅;\n  succs: ssas: \[\d+, \d+, \d+\], slots: ∅, names: ∅;\n  assign @: \[\d, \d+\]", str)
        @test occursin(r"\d+ preds: ssas: \[\d+\], slots: ∅, names: \[:s\];\n\d+ succs: ssas: ∅, slots: ∅, names: \[:s\];", str)
        LoweredCodeUtils.print_with_code(io, src, cl)
        str = String(take!(io))
        if isdefined(Base.IRShow, :show_ir_stmt)
            @test occursin(r"slot 1:\n  preds: ssas: \[\d+, \d+\], slots: ∅, names: ∅;\n  succs: ssas: \[\d+, \d+, \d+\], slots: ∅, names: ∅;\n  assign @: \[\d+, \d+\]", str)
            @test occursin("# see name s", str)
            @test occursin("# see slot 1", str)
            @test occursin(r"# preds: ssas: \[\d+\], slots: ∅, names: \[:s\]; succs: ssas: ∅, slots: ∅, names: \[:s\];", str)
        else
            @test occursin("No IR statement printer", str)
        end
        # CodeEdges
        edges = CodeEdges(src)
        show(io, edges)
        str = String(take!(io))
        @test occursin(r"s: assigned on \[\d, \d+\], depends on \[\d+\], and used by \[\d+, \d+, \d+\]", str)
        @test count(occursin("statement $i depends on [1, $(i-1), $(i+1)] and is used by [1, $(i+1)]", str) for i = 1:length(src.code)) == 1
        LoweredCodeUtils.print_with_code(io, src, edges)
        str = String(take!(io))
        if isdefined(Base.IRShow, :show_ir_stmt)
            @test occursin(r"s: assigned on \[\d, \d+\], depends on \[\d+\], and used by \[\d+, \d+, \d+\]", str)
            @test count(occursin("preds: [1, $(i-1), $(i+1)], succs: [1, $(i+1)]", str) for i = 1:length(src.code)) == 1
        else
            @test occursin("No IR statement printer", str)
        end
        # Works with Frames too
        frame = Frame(ModSelective, ex)
        edges = CodeEdges(frame.framecode.src)
        LoweredCodeUtils.print_with_code(io, frame, edges)
        str = String(take!(io))
        if isdefined(Base.IRShow, :show_ir_stmt)
            @test occursin(r"s: assigned on \[\d, \d+\], depends on \[\d+\], and used by \[\d+, \d+, \d+\]", str)
            @test count(occursin("preds: [1, $(i-1), $(i+1)], succs: [1, $(i+1)]", str) for i = 1:length(src.code)) == 1
        else
            @test occursin("No IR statement printer", str)
        end
    end
end

@testset "selective interpretation of toplevel definitions" begin
    gen_mock_module() = Core.eval(@__MODULE__, :(module $(gensym(:LoweredCodeUtilsTestMock)) end))
    function check_toplevel_definition_interprete(ex, defs, undefs)
        m = gen_mock_module()
        lwr = Meta.lower(m, ex)
        src = first(lwr.args)
        stmts = src.code
        edges = CodeEdges(src)

        isrq = lines_required!(istypedef.(stmts), src, edges)
        frame = Frame(m, src)
        selective_eval_fromstart!(frame, isrq, #= toplevel =# true)

        for def in defs; @test isdefined(m, def); end
        for undef in undefs; @test !isdefined(m, undef); end
    end

    @testset "case: $(i), interpret: $(defs), ignore $(undefs)" for (i, ex, defs, undefs) in (
            (1, :(abstract type Foo end), (:Foo,), ()),

            (2, :(struct Foo end), (:Foo,), ()),

            (3, quote
                struct Foo
                    val
                end
            end, (:Foo,), ()),

            (4, quote
                struct Foo{T}
                    val::T
                    Foo(v::T) where {T} = new{T}(v)
                end
            end, (:Foo,), ()),

            (5, :(primitive type Foo 32 end), (:Foo,), ()),

            (6, quote
                abstract type Foo end
                struct Foo1 <: Foo end
                struct Foo2 <: Foo end
            end, (:Foo, :Foo1, :Foo2), ()),

            (7, quote
                struct Foo
                    v
                    Foo(f) = new(f())
                end

                foo = Foo(()->throw("don't interpret me"))
            end, (:Foo,), (:foo,)),

            # https://github.com/JuliaDebug/LoweredCodeUtils.jl/issues/47
            (8, quote
                struct Foo
                    b::Bool
                    Foo(b) = new(b)
                end

                foo = Foo(false)
            end, (:Foo,), (:foo,)),

            # https://github.com/JuliaDebug/LoweredCodeUtils.jl/pull/48
            # we shouldn't make `add_links!` recur into `QuoteNode`, otherwise the variable
            # `bar` will be selected as a requirement for `Bar1` (, which has "bar" field)
            (9, quote
                abstract type Bar end
                struct Bar1 <: Bar
                    bar
                end

                r = (throw("don't interpret me"); rand(10000000000000000))
                bar = Bar1(r)
                show(bar)
            end, (:Bar, :Bar1), (:r, :bar))
        )

        check_toplevel_definition_interprete(ex, defs, undefs)
    end
end
