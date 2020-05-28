module LoweredCodeUtils

if isdefined(Base, :Experimental) && isdefined(Base.Experimental, Symbol("@optlevel"))
    @eval Base.Experimental.@optlevel 1
end

using Core: SimpleVector, CodeInfo, NewvarNode, GotoNode
using Base.Meta: isexpr
using JuliaInterpreter
using JuliaInterpreter: SSAValue, SlotNumber, Frame
using JuliaInterpreter: @lookup, moduleof, pc_expr, step_expr!, is_global_ref, is_quotenode, whichtt,
                        next_until!, finish_and_return!, get_return, nstatements, codelocation

const SSAValues = Union{Core.Compiler.SSAValue, JuliaInterpreter.SSAValue}

const structheads = VERSION >= v"1.5.0-DEV.702" ? () : (:struct_type, :abstract_type, :primitive_type)
const trackedheads = (:method, structheads...)

export signature, rename_framemethods!, methoddef!, methoddefs!, bodymethod, CodeEdges,
       lines_required, lines_required!, selective_eval!, selective_eval_fromstart!

include("utils.jl")
include("signatures.jl")
include("codeedges.jl")

# precompilation

if ccall(:jl_generating_output, Cint, ()) == 1
    kwdefine = NamedTuple{(:define,),Tuple{Bool}}
    for ct in (Vector{Any}, Set{Any})
        f = methoddef!
        m = which(f, Tuple{Function, ct, Frame, Expr, Int})
        @assert precompile(Tuple{typeof(f), Function, ct, Frame, Expr, Int})
        mbody = bodymethod(m)
        # @assert precompile(Tuple{mbody.sig.parameters[1], Bool, typeof(f), Function, ct, Frame, Expr, Int})
        @assert precompile(Tuple{Core.kwftype(typeof(f)), kwdefine, typeof(f), Function, ct, Frame, Expr, Int})
        f = methoddefs!
        @assert precompile(Tuple{typeof(f), Any, ct, Frame})
        @assert precompile(Tuple{Core.kwftype(typeof(f)), kwdefine, typeof(f), Function, ct, Frame})
    end
    @assert precompile(Tuple{typeof(rename_framemethods!), Any, Frame, Dict{Symbol,MethodInfo},
                             Vector{NamedTuple{(:linetop, :linebody, :callee, :caller),Tuple{Int64,Int64,Symbol,Union{Bool, Symbol}}}},
                             Dict{Symbol,Union{Bool, Symbol}}})
    @assert precompile(Tuple{typeof(identify_framemethod_calls), Frame})
    @assert precompile(Tuple{typeof(callchain), Vector{NamedTuple{(:linetop, :linebody, :callee, :caller),Tuple{Int64,Int64,Symbol,Union{Bool, Symbol}}}}})

    @assert precompile(CodeEdges, (CodeInfo,))
    @assert precompile(add_links!, (Pair{JuliaInterpreter.SSAValue,Links}, Any, CodeLinks))
    @assert precompile(add_links!, (Pair{JuliaInterpreter.SlotNumber,Links}, Any, CodeLinks))
    @assert precompile(add_links!, (Pair{Symbol,Links}, Any, CodeLinks))
    @assert precompile(lines_required!, (Vector{Bool}, Set{NamedVar}, CodeInfo, CodeEdges))
end

end # module
