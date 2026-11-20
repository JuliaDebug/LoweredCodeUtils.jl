Base.Experimental.@optlevel 1

using Core: MethodTable, SimpleVector
using Core.IR: CodeInfo, GotoIfNot, GotoNode, MethodInstance, ReturnNode
@static if isdefined(Core.IR, :EnterNode)
    using Core.IR: EnterNode
end
using .CC:
    BasicBlock, CFG, compute_basic_blocks, construct_postdomtree, nearest_common_dominator

@static if isdefined(CC, :IRShow)
    using .CC: IRShow
else
    using Base: IRShow
end

using Base.Meta: isexpr

const SSAValues = Union{Core.IR.SSAValue, JuliaInterpreter.SSAValue}

const trackedheads = (:method,)    # Revise uses this (for now), don't delete; also update test/hastrackedexpr if this list gets expanded
const structdecls = (:_structtype, :_abstracttype, :_primitivetype)

export bodymethod, methoddef!, methoddefs!, rename_framemethods!, signature
export CodeEdges, SelectiveEvalController, SelectiveInterpreter,
       lines_required, lines_required!, selective_eval!, selective_eval_fromstart!

include("utils.jl")
include("signatures.jl")
include("codeedges.jl")
