using LoweredCodeUtils
using LoweredCodeUtils.JuliaInterpreter
using JuliaInterpreter: is_global_ref, is_quotenode
using Test

# # Utilities for finding statements corresponding to particular calls
# function callpredicate(@nospecialize(stmt), fsym)
#     isa(stmt, Expr) || return false
#     head = stmt.head
#     if head === :(=)
#         return callpredicate(stmt.args[2], fsym)
#     end
#     return LoweredCodeUtils.iscallto(stmt, fsym)
# end

function hastrackedexpr(stmt; heads=LoweredCodeUtils.trackedheads)
    haseval = false
    if isa(stmt, Expr)
        if stmt.head === :call
            haseval = JuliaInterpreter.hasarg(isequal(:eval), stmt.args)
            f = stmt.args[1]
            is_global_ref(f, Core, :_typebody!) && return true, haseval
            if isdefined(Core, :_typebody!)
                is_quotenode(f, Core._typebody!) && return true, haseval
            end
            is_global_ref(f, Core, :_setsuper!) && return true, haseval
            if isdefined(Core, :_setsuper!)
                is_quotenode(f, Core._setsuper!) && return true, haseval
            end
            f === :include && return true, haseval
        end
        stmt.head ∈ heads && return true, haseval
        if stmt.head == :thunk
            any(s->any(hastrackedexpr(s; heads=heads)), stmt.args[1].code) && return true, haseval
        end
    end
    return false, haseval
end

function minimal_evaluation(src::Core.CodeInfo, edges::CodeEdges)
    musteval = fill(false, length(src.code))
    for (i, stmt) in enumerate(src.code)
        if !musteval[i]
            musteval[i], haseval = hastrackedexpr(stmt)
            if haseval
                musteval[edges.succs[i]] .= true
            end
        end
    end
    # All tracked expressions are marked. Now add their dependencies.
    lines_required!(musteval, src, edges)
    # Struct definitions likely omitted const/global. Look for them via name.
    for (name, var) in edges.byname
        if !isempty(var.assigned) && any(i->musteval[i], var.succs)
            foreach(var.succs) do i
                stmt = src.code[i]
                if isa(stmt, Expr)
                    if stmt.head === :global || stmt.head === :const
                        musteval[i] = true
                    end
                end
            end
        end
    end
    return musteval
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
    lwr = Meta.lower(ModSelective, ex)
    frame = JuliaInterpreter.prepare_thunk(ModSelective, lwr)
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
    lwr = Meta.lower(ModSelective, ex)
    frame = JuliaInterpreter.prepare_thunk(ModSelective, lwr)
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
    lwr = Meta.lower(ModSelective, ex)
    frame = JuliaInterpreter.prepare_thunk(ModSelective, lwr)
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
    lwr = Meta.lower(ModSelective, ex)
    frame = JuliaInterpreter.prepare_thunk(ModSelective, lwr)
    src = frame.framecode.src
    edges = CodeEdges(src)
    # Mark just the load of Core.eval
    haseval(stmt) = isa(stmt, Expr) && JuliaInterpreter.hasarg(isequal(:eval), stmt.args)
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
    frame = JuliaInterpreter.prepare_thunk(ModSelective, ex)
    JuliaInterpreter.finish_and_return!(frame, true)
    @test ModSelective.k11 == 11
    @test 3 <= ModSelective.s11 <= 15
    Core.eval(ModSelective, :(k11 = 0; s11 = -1))
    edges = CodeEdges(frame.framecode.src)
    isrequired = lines_required(:s11, frame.framecode.src, edges)
    selective_eval_fromstart!(frame, isrequired, true)
    @test ModSelective.k11 == 0
    @test 3 <= ModSelective.s11 <= 15

    # Control-flow in a structure definition
    ex = :(abstract type StructParent{T, N} <: AbstractArray{T, N} end)
    frame = JuliaInterpreter.prepare_thunk(ModSelective, ex)
    src = frame.framecode.src
    edges = CodeEdges(src)
    isrequired = minimal_evaluation(src, edges)
    selective_eval_fromstart!(frame, isrequired, true)
    @test supertype(ModSelective.StructParent) === AbstractArray
    # Also check redefinition (it's OK when the definition doesn't change)
    Core.eval(ModEval, ex)
    frame = JuliaInterpreter.prepare_thunk(ModEval, ex)
    src = frame.framecode.src
    edges = CodeEdges(src)
    isrequired = minimal_evaluation(src, edges)
    selective_eval_fromstart!(frame, isrequired, true)
    @test supertype(ModEval.StructParent) === AbstractArray

    # Anonymous functions
    ex = :(max_values(T::Union{map(X -> Type{X}, Base.BitIntegerSmall_types)...}) = 1 << (8*sizeof(T)))
    frame = JuliaInterpreter.prepare_thunk(ModSelective, ex)
    src = frame.framecode.src
    edges = CodeEdges(src)
    isrequired = fill(false, length(src.code))
    @assert Meta.isexpr(src.code[end-1], :method, 3)
    isrequired[end-1] = true
    lines_required!(isrequired, src, edges)
    selective_eval_fromstart!(frame, isrequired, true)
    @test ModSelective.max_values(Int16) === 65536

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
        VERSION >= v"1.1" && @test occursin(r"s:\n  preds: ssas: \[\d+\], slots: ∅, names: ∅;\n  succs: ssas: \[\d+, \d+, \d+\], slots: ∅, names: ∅;\n  assign @: \[\d, \d+\]", str)
        VERSION >= v"1.1" && @test occursin(r"\d+ preds: ssas: \[\d+\], slots: ∅, names: \[:s\];\n\d+ succs: ssas: ∅, slots: ∅, names: \[:s\];", str)
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
        VERSION >= v"1.1" && @test occursin(r"s: assigned on \[\d, \d+\], depends on \[\d+\], and used by \[\d+, \d+, \d+\]", str)
        VERSION >= v"1.1" && @test count(occursin("statement $i depends on [1, $(i-1), $(i+1)] and is used by [1, $(i+1)]", str) for i = 1:length(src.code)) == 1
        LoweredCodeUtils.print_with_code(io, src, edges)
        str = String(take!(io))
        if isdefined(Base.IRShow, :show_ir_stmt)
            @test occursin(r"s: assigned on \[\d, \d+\], depends on \[\d+\], and used by \[\d+, \d+, \d+\]", str)
            @test count(occursin("preds: [1, $(i-1), $(i+1)], succs: [1, $(i+1)]", str) for i = 1:length(src.code)) == 1
        else
            @test occursin("No IR statement printer", str)
        end
    end
end
