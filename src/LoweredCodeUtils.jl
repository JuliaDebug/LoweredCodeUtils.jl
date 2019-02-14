module LoweredCodeUtils

using Core: SimpleVector, CodeInfo
using Base.Meta: isexpr
using JuliaInterpreter
using JuliaInterpreter: JuliaProgramCounter, @lookup, moduleof, pc_expr, _step_expr!

export whichtt, signature, methoddef!

"""
    method = whichtt(tt)

Like `which` except it operates on the complete tuple-type `tt`.
"""
function whichtt(tt)
    m = ccall(:jl_gf_invoke_lookup, Any, (Any, UInt), tt, typemax(UInt))
    m === nothing && return nothing
    return m.func::Method
end

"""
    iscallto(stmt, name)

Returns `true` is `stmt` is a call expression to `name`.
"""
function iscallto(stmt, name)
    if isexpr(stmt, :call)
        a = stmt.args[1]
        a == name && return true
        return isa(a, GlobalRef) && a.mod == Core && a.name == :_apply && stmt.args[2] == name
    end
    return false
end

"""
    getcallee(stmt)

Returns the function (or Symbol) being called in a :call expression.
"""
function getcallee(stmt)
    if isexpr(stmt, :call)
        a = stmt.args[1]
        isa(a, GlobalRef) && a.mod == Core && a.name == :_apply && return stmt.args[2]
        return a
    end
    error(stmt, " is not a call expression")
end

"""
    nextpc = next_or_nothing(frame, pc)

Advance the program counter. If `frame` is finished, `nextpc` will be `nothing`.
"""
next_or_nothing(frame, pc) = convert(Int, pc) < length(frame.code.code.code) ? pc+1 : nothing

"""
    nextpc = skip_until(predicate, frame, pc)

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

function signature(sigsv::SimpleVector)
    sigp, sigtv = sigsv
    sig = Tuple{sigp...}
    for i = length(sigtv):-1:1
        sig = UnionAll(sigtv[i], sig)
    end
    return sig
end

"""
    sigt, lastpc = signature(stack, frame, pc)

Compute the signature-type `sigt` of a method whose definition in `frame` starts at `pc`.
Generally, `pc` should point to the `Expr(:method, methname)` statement, in which case
`lastpc` is the final statement number in `frame` that is part of the signature
(i.e, the line above the 3-argument `:method` expression).
Alternatively, `pc` can point to the 3-argument `:method` expression,
as long as all the relevant SSAValues have been assigned.
In this case, `lastpc == pc`.

If no 3-argument `:method` expression is found, `sigt` will be `nothing`.
"""
function signature(stack, frame, stmt, pc::JuliaProgramCounter)
    lastpc = pc
    while !isexpr(stmt, :method, 3)  # wait for the 3-arg version
        if isexpr(stmt, :thunk) && isanonymous_typedef(stmt.args[1])
            lastpc = pc = define_anonymous(stack, frame, stmt, pc)
        else
            lastpc = pc
            pc = _step_expr!(stack, frame, stmt, pc, true)
            pc === nothing && return nothing, lastpc
        end
        stmt = pc_expr(frame, pc)
    end
    sigsv = @lookup(frame, stmt.args[2])::SimpleVector
    sigt = signature(sigsv)
    return sigt, lastpc
end
signature(stack, frame, pc::JuliaProgramCounter) = signature(stack, frame, pc_expr(frame, pc), pc)

##
## Detecting anonymous functions. These start with a :thunk expr and have a characteristic CodeInfo
##
function isanonymous_typedef(code::CodeInfo)
    length(code.code) >= 4 || return false
    stmt = code.code[end-1]
    isexpr(stmt, :struct_type) || return false
    name = stmt.args[1]::Symbol
    return startswith(String(name), "##")
end

function define_anonymous(stack, frame, stmt, pc)
    while !isexpr(stmt, :method)
        pc = _step_expr!(stack, frame, stmt, pc, true)
        stmt = pc_expr(frame, pc)
    end
    return _step_expr!(stack, frame, stmt, pc, true)  # also define the method
end

##
## Deal with gensymmed names, https://github.com/JuliaLang/julia/issues/30908
## This handles the situation in which a method is created using a different gensym
## than when this method was last lowered & evaled.
##

function get_parentname(name)
    isa(name, Expr) && return name
    isa(name, Symbol) || error("unhandled name type ", typeof(name))
    namestring = String(name)
    if namestring[1] == '#'
        pidx = 1
        idx = nextind(namestring, pidx)
        while namestring[idx] != '#'
            pidx = idx
            idx = nextind(namestring, idx)
        end
        parentname = Symbol(namestring[2:pidx])
    else
        parentname = name
    end
    return parentname
end

"""
    pctop, isgen = find_corrected_name(frame, pc, name, parentname)

Scans forward from `pc` in `frame` until a method is found that calls `name`.
`pctop` points to the beginning of that method's signature.
`isgen` is true if `name` corresponds to sa GeneratedFunctionStub.

Alternatively, this returns `nothing` if `pc` does not appear to point to either
a keyword or generated method.
"""
function find_corrected_name(frame, pc, name, parentname)
    stmt = pc_expr(frame, pc)
    while !isexpr(stmt, :method, 1) || stmt.args[1] != parentname
        isexpr(stmt, :method, 1) && stmt.args[1] != name && break
        pc += 1
        stmt = pc_expr(frame, pc)
    end
    pctop = pc # keep track of the beginning of the signature
    if stmt.args[1] != name && stmt.args[1] != parentname
        # This might be the GeneratedFunctionStub for a @generated method
        newname = stmt.args[1]
        while !isexpr(stmt, :method, 3) || stmt.args[1] != newname
            pc += 1
            stmt = pc_expr(frame, pc)
        end
        body = stmt.args[3]
        bodystmt = body.code[1]
        (isexpr(bodystmt, :meta) && bodystmt.args[1] == :generated) || return nothing
        return pctop, true
    else
        # Keyword arg function
        while true
            while !isexpr(stmt, :method, 3) || stmt.args[1] != parentname
                pc += 1
                stmt = pc_expr(frame, pc)
            end
            body = stmt.args[3]
            bodystmt = body.code[end-1]  # the line before the final return
            iscallto(bodystmt, name) && return pctop, false
            pc += 1
            pctop = pc
            stmt = pc_expr(frame, pc)
        end
    end
end

"""
    replacename!(stmts, oldname=>newname)

Replace a Symbol `oldname` with `newname` in `stmts`.
"""
function replacename!(ex::Expr, pr)
    replacename!(ex.args, pr)
    return ex
end

function replacename!(args::Vector{Any}, pr)
    oldname, newname = pr
    for i = 1:length(args)
        a = args[i]
        if isa(a, Expr)
            replacename!(a, pr)
        elseif isa(a, CodeInfo)
            replacename!(a.code, pr)
        elseif isa(a, QuoteNode) && a.value == oldname
            args[i] = QuoteNode(newname)
        elseif a == oldname
            args[i] = newname
        end
    end
    return args
end

function correct_name!(stack, frame, pc, name, parentname)
    # Get the correct name (the one that's actively running)
    nameinfo = find_corrected_name(frame, pc, name, parentname)
    if nameinfo === nothing
        pc = skip_until(stmt->isexpr(stmt, :method, 3), frame, pc)
        lastidx = convert(Int, pc)
        pc = next_or_nothing(frame, pc)
    else
        pctop, isgen = nameinfo
        sigtparent, lastpcparent = signature(stack, frame, pctop)
        methparent = whichtt(sigtparent)::Method
        if isgen
            cname = nameof(methparent.generator.gen)
        else
            bodyparent = Base.uncompressed_ast(methparent)
            bodystmt = bodyparent.code[end-1]
            @assert isexpr(bodystmt, :call)
            ref = getcallee(bodystmt)
            isa(ref, GlobalRef) || @show ref typeof(ref)
            @assert isa(ref, GlobalRef)
            @assert ref.mod == moduleof(frame)
            cname = ref.name
        end
        # Swap in the correct name
        replacename!(frame.code.code.code, name=>cname)
        name = parentname = pc_expr(frame, pctop).args[1]
    end
    return name, parentname, pc
end

"""
    linespan, pc = methoddef!(signatures, stack, frame, pc)

Collect all signatures and return the span of all the methods generated by a single definition
(including default-args and keyword-arg methods). `pc` should point to a 1-argument
`:method` expression.
"""
function methoddef!(signatures, stack, frame, stmt, pc::JuliaProgramCounter)
    isexpr(stmt, :method) || isexpr(stmt, :struct_type) || error("expected method, got ", stmt)
    name = stmt.args[1]
    if isa(name, Bool)
        parentname = name
    else
        parentname = get_parentname(name)  # e.g., name = #foo#7 and parentname = foo
    end
    firstidx = convert(Int, pc)
    codelocs = frame.code.code.codelocs  # methods from the same definition have the same starting line number
    srcloc = codelocs[firstidx]          # ...though we also need to check names
    local lastidx
    while true
        if isexpr(stmt, :method) && length(stmt.args) == 1 && name != parentname
            if get_parentname(name) != parentname
                # We've moved on to a new method. If this gets triggered you probably
                # need to be splitting more before lowering, but it's safer to have this.
                @warn "split $frame"
                return firstidx:lastidx, pc
            end
            name, parentname, pc = correct_name!(stack, frame, pc, name, parentname)
        end
        sigt, pc = signature(stack, frame, stmt, pc)
        stmt = pc_expr(frame, pc)
        while !isexpr(stmt, :method, 3)
            lastidx = convert(Int, pc)
            pc = next_or_nothing(frame, pc)
            pc === nothing && return firstidx:lastidx, pc
            stmt = pc_expr(frame, pc)
        end
        lastidx = convert(Int, pc)
        sigt === nothing && return firstidx:lastidx, next_or_nothing(frame, pc)
        meth = whichtt(sigt)
        isa(meth, Method) && push!(signatures, meth.sig)
        pc = next_or_nothing(frame, pc)
        pc === nothing && return firstidx:lastidx, pc
        stmt = pc_expr(frame, pc)
    end
end
methoddef!(signatures, stack, frame, pc::JuliaProgramCounter) =
    methoddef!(signatures, stack, frame, pc_expr(frame, pc), pc)
function methoddef!(signatures, stack, frame)
    pc = frame.pc[]
    pc = skip_until(stmt->isexpr(stmt, :method, 1), frame, pc)
    methoddef!(signatures, stack, frame, pc)
end

end # module
