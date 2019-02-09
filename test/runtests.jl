using LoweredCodeUtils, JuliaInterpreter
using Core: CodeInfo
using Test

module Lowering end

@testset "LoweredCodeUtils.jl" begin
    stack = JuliaStackFrame[]
    signatures = Set{Any}()
    newcode = CodeInfo[]
    for ex in (:(f(x::Int8; y=0) = y),
               :(f(x::Int16; y::Int=0) = 2),
               :(f(x::Int32; y="hello", z::Int=0) = 3),
               :(f(x::Int64;) = 4),
               :(f(x::Array{Float64,K}; y::Int=0) where K = K),
               # Keyword & default positional args
               :(g(x, y="hello"; z::Int=0) = 1),
               # Generated methods
               quote
                   @generated function h(x)
                       if x <: Integer
                           return :(x ^ 2)
                       else
                           return :(x)
                       end
                   end
               end,
               quote
                   function h(x::Int, y)
                       if @generated
                           return y <: Integer ? :(x*y) : :(x+y)
                       else
                           return 2x+3y
                       end
                   end
               end)
        Core.eval(Lowering, ex)
        frame = JuliaInterpreter.prepare_toplevel(Lowering, ex)
        methoddef!(signatures, stack, frame)
        push!(newcode, frame.code.code)
    end

    nms = names(Lowering; all=true)
    modeval, modinclude = getfield(Lowering, :eval), getfield(Lowering, :include)
    failed = []
    for fsym in nms
        f = getfield(Lowering, fsym)
        isa(f, Base.Callable) || continue
        (f === modeval || f === modinclude) && continue
        for m in methods(f)
            if m.sig ∉ signatures
                push!(failed, m.sig)
            end
        end
    end
    @test isempty(failed)
    # Ensure that all names are properly resolved
    for code in newcode
        Core.eval(Lowering, code)
    end
    nms2 = names(Lowering; all=true)
    @test nms2 == nms
    @test Lowering.f(Int8(0)) == 0
    @test Lowering.f(Int8(0); y="LCU") == "LCU"
    @test Lowering.f(Int16(0)) == Lowering.f(Int16(0), y=7) == 2
    @test Lowering.f(Int32(0)) == Lowering.f(Int32(0); y=22) == Lowering.f(Int32(0); y=:cat, z=5) == 3
    @test Lowering.f(Int64(0)) == 4
    @test Lowering.f(rand(3,3)) == Lowering.f(rand(3,3); y=5) == 2
    @test Lowering.g(0) == Lowering.g(0,"LCU") == Lowering.g(0; z=5) == Lowering.g(0,"LCU"; z=5) == 1
    @test Lowering.h(2) == 4
    @test Lowering.h(2.0) == 2.0
    @test Lowering.h(2, 3) == 6
    @test Lowering.h(2, 3.0) == 5.0

    # Don't be deceived by inner methods
    stack = JuliaStackFrame[]
    signatures = []
    ex = quote
        function fouter(x)
            finner(::Float16) = 2x
            return finner(Float16(1))
        end
    end
    Core.eval(Lowering, ex)
    frame = JuliaInterpreter.prepare_toplevel(Lowering, ex)
    methoddef!(signatures, stack, frame)
    @test length(signatures) == 1
    @test LoweredCodeUtils.whichtt(signatures[1]) == first(methods(Lowering.fouter))
end
