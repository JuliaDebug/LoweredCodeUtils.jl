using LoweredCodeUtils, JuliaInterpreter
using Core: CodeInfo
using Base.Meta: isexpr
using Test

module Lowering
struct Caller end
struct Gen{T} end
end

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
               end,
               # Generated constructors
               quote
                   function Gen{T}(x) where T
                       if @generated
                           return T <: Integer ? :(x^2) : :(2x)
                       else
                           return 7x
                       end
                   end
               end,
               # Conditional methods
               quote
                   if 0.8 > 0.2
                       fctrue(x) = 1
                   else
                       fcfalse(x) = 1
                   end
               end,
               # Call methods
               :((::Caller)(x::String) = length(x)),
               )
        Core.eval(Lowering, ex)
        frame = JuliaInterpreter.prepare_thunk(Lowering, ex)
        pc = methoddefs!(signatures, stack, frame; define=false)
        push!(newcode, frame.code.code)
    end

    # Manually add the signature for the Caller constructor, since that was defined
    # outside of manual lowering
    push!(signatures, Tuple{Type{Lowering.Caller}})

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
    @test Lowering.fctrue(0) == 1
    @test_throws UndefVarError Lowering.fcfalse(0)
    @test (Lowering.Caller())("Hello, world") == 12
    g = Lowering.Gen{Float64}
    @test g(3) == 6

    # Don't be deceived by inner methods
    empty!(stack)
    signatures = []
    ex = quote
        function fouter(x)
            finner(::Float16) = 2x
            return finner(Float16(1))
        end
    end
    Core.eval(Lowering, ex)
    frame = JuliaInterpreter.prepare_thunk(Lowering, ex)
    methoddefs!(signatures, stack, frame; define=false)
    @test length(signatures) == 1
    @test LoweredCodeUtils.whichtt(signatures[1]) == first(methods(Lowering.fouter))

    # Check positioning in correct_name!
    ex = :(g(x::Int8; y=0) = y)
    Core.eval(Lowering, ex)
    frame = JuliaInterpreter.prepare_thunk(Lowering, ex)
    pc = frame.pc[]
    stmt = JuliaInterpreter.pc_expr(frame, pc)
    name = LoweredCodeUtils.methodname(stmt.args[1])
    parentname = LoweredCodeUtils.get_parentname(name)
    name, pc = LoweredCodeUtils.correct_name!(empty!(stack), frame, pc, name, parentname)
    @test name == parentname

    # Check output of methoddef!
    frame = JuliaInterpreter.prepare_thunk(Lowering, :(function nomethod end))
    ret = methoddef!(empty!(signatures), empty!(stack), frame; define=true)
    @test isempty(signatures)
    @test ret === nothing
    frame = JuliaInterpreter.prepare_thunk(Lowering, :(function amethod() nothing end))
    ret = methoddef!(empty!(signatures), empty!(stack), frame; define=true)
    @test !isempty(signatures)
    @test isa(ret, NTuple{2,JuliaInterpreter.JuliaProgramCounter})

    # Anonymous functions in method signatures
    ex = :(max_values(T::Union{map(X -> Type{X}, Base.BitIntegerSmall_types)...}) = 1 << (8*sizeof(T)))  # base/abstractset.jl
    frame = JuliaInterpreter.prepare_thunk(Base, ex)
    signatures = Set{Any}()
    methoddef!(signatures, stack, frame; define=false)
    @test length(signatures) == 1
    @test first(signatures) == which(Base.max_values, Tuple{Type{Int16}}).sig

    # define
    ex = :(fdefine(x) = 1)
    frame = JuliaInterpreter.prepare_thunk(Lowering, ex)
    empty!(signatures)
    empty!(stack)
    methoddefs!(signatures, stack, frame; define=false)
    @test_throws MethodError Lowering.fdefine(0)
    frame = JuliaInterpreter.prepare_thunk(Lowering, ex)
    empty!(signatures)
    empty!(stack)
    methoddefs!(signatures, stack, frame; define=true)
    @test Lowering.fdefine(0) == 1
end
