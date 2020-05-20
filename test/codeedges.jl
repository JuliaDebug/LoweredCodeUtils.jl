using LoweredCodeUtils
using LoweredCodeUtils.JuliaInterpreter
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

    # TODO: add printing tests
    # LoweredCodeUtils.print_with_code(stdout, src, isrequired)
end
