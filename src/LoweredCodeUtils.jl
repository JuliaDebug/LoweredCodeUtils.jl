module LoweredCodeUtils

using JuliaInterpreter
using JuliaInterpreter: SSAValue, SlotNumber, Frame
using JuliaInterpreter: @lookup, moduleof, pc_expr, step_expr!, is_global_ref, is_quotenode, whichtt,
                        next_until!, finish_and_return!, get_return, nstatements, codelocation


include("core.jl")

end # module
