const AnySSAValue = Union{Core.Compiler.SSAValue,JuliaInterpreter.SSAValue}
const AnySlotNumber = Union{Core.Compiler.SlotNumber,JuliaInterpreter.SlotNumber}

isssa(stmt) = isa(stmt, Core.Compiler.SSAValue) | isa(stmt, JuliaInterpreter.SSAValue)
isslotnum(stmt) = isa(stmt, Core.Compiler.SlotNumber) | isa(stmt, JuliaInterpreter.SlotNumber)

"""
    iscallto(stmt, name)

Returns `true` is `stmt` is a call expression to `name`.
"""
function iscallto(@nospecialize(stmt), name)
    if isexpr(stmt, :call)
        a = stmt.args[1]
        a === name && return true
        return is_global_ref(a, Core, :_apply) && stmt.args[2] === name
    end
    return false
end

"""
    getcallee(stmt)

Returns the function (or Symbol) being called in a :call expression.
"""
function getcallee(@nospecialize(stmt))
    if isexpr(stmt, :call)
        a = stmt.args[1]
        is_global_ref(a, Core, :_apply) && return stmt.args[2]
        return a
    end
    error(stmt, " is not a call expression")
end

ismethod(frame::Frame)  = ismethod(pc_expr(frame))
ismethod3(frame::Frame) = ismethod3(pc_expr(frame))

ismethod(stmt)  = isexpr(stmt, :method)
ismethod1(stmt) = isexpr(stmt, :method, 1)
ismethod3(stmt) = isexpr(stmt, :method, 3)

"""
    nextpc = next_or_nothing(frame, pc)
    nextpc = next_or_nothing!(frame)

Advance the program counter without executing the corresponding line.
If `frame` is finished, `nextpc` will be `nothing`.
"""
next_or_nothing(frame, pc) = pc < nstatements(frame.framecode) ? pc+1 : nothing
function next_or_nothing!(frame)
    pc = frame.pc
    if pc < nstatements(frame.framecode)
        frame.pc = pc = pc + 1
        return pc
    end
    return nothing
end

"""
    nextpc = skip_until(predicate, frame, pc)
    nextpc = skip_until!(predicate, frame)

Advance the program counter until `predicate(stmt)` return `true`.
"""
function skip_until(predicate, frame, pc)
    stmt = pc_expr(frame, pc)
    while !predicate(stmt)
        pc = next_or_nothing(frame, pc)
        pc === nothing && return nothing
        stmt = pc_expr(frame, pc)
    end
    return pc
end
function skip_until!(predicate, frame)
    pc = frame.pc
    stmt = pc_expr(frame, pc)
    while !predicate(stmt)
        pc = next_or_nothing!(frame)
        pc === nothing && return nothing
        stmt = pc_expr(frame, pc)
    end
    return pc
end

function sparam_ub(meth::Method)
    typs = []
    sig = meth.sig
    while sig isa UnionAll
        push!(typs, Symbol(sig.var.ub))
        sig = sig.body
    end
    return Core.svec(typs...)
end

showempty(list) = isempty(list) ? '∅' : list

# Smooth the transition between Core.Compiler and Base
rng(bb::Core.Compiler.BasicBlock) = (r = bb.stmts; return Core.Compiler.first(r):Core.Compiler.last(r))
