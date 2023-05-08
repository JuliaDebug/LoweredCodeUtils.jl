using Test

# using LoweredCodeUtils
# @testset "Ambiguity" begin
#     @test isempty(detect_ambiguities(LoweredCodeUtils, LoweredCodeUtils.JuliaInterpreter, Base, Core))
# end

@testset "LoweredCodeUtils.jl" begin
    @static if VERSION ≥ v"1.8"
        @testset "signatures.jl" include("signatures.jl")
        @testset "codeedges.jl" include("codeedges.jl")
    else
        include("signatures.jl")
        include("codeedges.jl")
    end
end
