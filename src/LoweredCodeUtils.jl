module LoweredCodeUtils

using Core: SimpleVector, CodeInfo, SSAValue
using Base.Meta: isexpr
using JuliaInterpreter
using JuliaInterpreter: JuliaProgramCounter, @lookup, moduleof, pc_expr, _step_expr!, isglobalref

export whichtt, signature, methoddef!, methoddefs!

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
        return isglobalref(a, Core, :_apply) && stmt.args[2] == name
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
        isglobalref(a, Core, :_apply) && return stmt.args[2]
        return a
    end
    error(stmt, " is not a call expression")
end

ismethod(stmt)  = isexpr(stmt, :method)
ismethod1(stmt) = isexpr(stmt, :method, 1)
ismethod3(stmt) = isexpr(stmt, :method, 3)

function methodname(name)
    isa(name, Symbol) && return name
    if isa(name, CodeInfo) && length(name.code) == 1 && isexpr(name.code[1], :return) && ismethod1(name.code[1].args[1])
        return name.code[1].args[1].args[1]
    end
    error("unhandled name type ", typeof(name))
end

"""
    nextpc = next_or_nothing(frame, pc)

Advance the program counter without executing the corresponding line.
If `frame` is finished, `nextpc` will be `nothing`.
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

"""
    sig = signature(sigsv::SimpleVector)

Compute a method signature from a suitable `SimpleVector`: `sigsv[1]` holds the signature
and `sigsv[2]` the `TypeVar`s.

# Example:

For `f(x::AbstractArray{T}) where T`, the corresponding `sigsv` is constructed as

    T = TypeVar(:T)
    sig1 = Core.svec(typeof(f), AbstractArray{T})
    sig2 = Core.svec(T)
    sigsv = Core.svec(sig1, sig2)
    sig = signature(sigsv)
"""
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

function minid(node, stmts, id)
    if isa(node, SSAValue)
        id = min(id, node.id)
        stmt = stmts[node.id]
        return minid(stmt, stmts, id)
    elseif isa(node, Expr)
        for a in node.args
            id = minid(a, stmts, id)
        end
    end
    return id
end

function signature_top(frame, stmt, pc)
    @assert ismethod3(stmt)
    return JuliaProgramCounter(minid(stmt.args[2], frame.code.code.code, convert(Int, pc)))
end

##
## Detecting anonymous functions. These start with a :thunk expr and have a characteristic CodeInfo
##
function isanonymous_typedef(code::CodeInfo)
    length(code.code) >= 4 || return false
    stmt = code.code[end-1]
    isexpr(stmt, :struct_type) || return false
    name = stmt.args[1]::Symbol
    return startswith(String(name), "#")
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
    name = methodname(name)
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
    while true
        while !ismethod3(stmt)
            pc = next_or_nothing(frame, pc)
            pc === nothing && return nothing
            stmt = pc_expr(frame, pc)
        end
        body = stmt.args[3]
        if stmt.args[1] != name && stmt.args[1] != parentname
            # This might be the GeneratedFunctionStub for a @generated method
            bodystmt = body.code[1]
            if isexpr(bodystmt, :meta) && bodystmt.args[1] == :generated
                return signature_top(frame, stmt, pc), true
            end
        elseif length(body.code) > 1
            bodystmt = body.code[end-1]  # the line before the final return
            iscallto(bodystmt, name) && return signature_top(frame, stmt, pc), false
        end
        pc = next_or_nothing(frame, pc)
        pc === nothing && return nothing
        stmt = pc_expr(frame, pc)
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
        methparent = whichtt(sigtparent)
        methparent === nothing && return name, pc  # caller isn't defined, no correction is needed
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
        if name != cname
            replacename!(frame.code.code.code, name=>cname)
        end
        name = pc_expr(frame, pctop-1).args[1]
    end
    return name, pc
end

"""
    ret = methoddef!(signatures, stack, frame, pc; define=true)

Compute the signature of a method definition. `pc` should point to a
`:method` expression. Upon exit, the new signature will be added to `signatures`.

There are several possible return values:

    pc, pc3 = ret

is the typical return. `pc` will point to the next statement to be executed, or be `nothing`
if there are no further statements in `frame`. `pc3` will point to the 3-argument `:method`
expression.

Alternatively,

    pc = ret

occurs for "empty method" expressions, e.g., `:(function foo end)`. `pc` will be `nothing`.

By default the method will be defined (evaluated). You can prevent this by setting `define=false`.
This is recommended if you are simply extracting signatures from code that has already been evaluated.

An important point is that `methoddef!` may, in some circumstances, change the names
of methods in `frame`.  The issues are described in https://github.com/JuliaLang/julia/issues/30908.
`methoddef!` will try to replace names with the ones that are currently active.
"""
function methoddef!(signatures, stack, frame, stmt, pc::JuliaProgramCounter; define=true)
    if ismethod3(stmt)
        pc3 = pc
        sigt, pc = signature(stack, frame, stmt, pc)
        meth = whichtt(sigt)
        if isa(meth, Method)
            push!(signatures, meth.sig)
        else
            # guard against busted lookup, e.g., https://github.com/JuliaLang/julia/issues/31112
            code = frame.code.code
            loc = code.linetable[code.codelocs[convert(Int, pc)]]
            ft = sigt.parameters[1]
            if !startswith(String(ft.name.name), "##")
                @warn "file $(loc.file), line $(loc.line): no method found for $sigt"
            end
        end
        return ( define ? _step_expr!(stack, frame, stmt, pc, true) : next_or_nothing(frame, pc) ), pc3
    end
    ismethod1(stmt) || error("expected method opening, got ", stmt)
    name = stmt.args[1]
    if isa(name, Bool)
        error("not valid for anonymous methods")
    end
    parentname = get_parentname(name)  # e.g., name = #foo#7 and parentname = foo
    nextstmt = pc_expr(frame, pc+1)
    if ismethod1(nextstmt)
        name = nextstmt.args[1]
    end
    if name != parentname
        name, endpc = correct_name!(stack, frame, pc, name, parentname)
    end
    while true  # methods containing inner methods may need multiple trips through this loop
        sigt, pc = signature(stack, frame, stmt, pc)
        stmt = pc_expr(frame, pc)
        while !isexpr(stmt, :method, 3)
            pc = next_or_nothing(frame, pc)  # this should not check define, we've probably already done this once
            pc === nothing && return pc   # this was just `function foo end`, signal "no def"
            stmt = pc_expr(frame, pc)
        end
        pc3 = pc
        name3 = stmt.args[1]
        sigt === nothing && (error("expected a signature"); return next_or_nothing(frame, pc)), pc3
        # Methods like f(x::Ref{<:Real}) that use gensymmed typevars will not have the *exact*
        # signature of the active method. So let's get the active signature.
        pc = define ? _step_expr!(stack, frame, stmt, pc, true) : next_or_nothing(frame, pc)
        meth = whichtt(sigt)
        isa(meth, Method) && push!(signatures, meth.sig) # inner methods are not visible
        name == name3 && return pc, pc3     # if this was an inner method we should keep going
        stmt = pc_expr(frame, pc)  # there *should* be more statements in this frame
    end
end
methoddef!(signatures, stack, frame, pc::JuliaProgramCounter; define=true) =
    methoddef!(signatures, stack, frame, pc_expr(frame, pc), pc; define=define)
function methoddef!(signatures, stack, frame; define=true)
    pc = frame.pc[]
    stmt = pc_expr(frame, pc)
    if !ismethod(stmt)
        pc = JuliaInterpreter.next_until!(ismethod, stack, frame, pc, true)
    end
    methoddef!(signatures, stack, frame, pc; define=define)
end

function methoddefs!(signatures, stack, frame; define=true)
    ret = methoddef!(signatures, stack, frame; define=define)
    pc = ret === nothing ? ret : ret[1]
    return _methoddefs!(signatures, stack, frame, pc; define=define)
end
function methoddefs!(signatures, stack, frame, pc::JuliaProgramCounter; define=true)
    ret = methoddef!(signatures, stack, frame, pc; define=define)
    pc = ret === nothing ? ret : ret[1]
    return _methoddefs!(signatures, stack, frame, pc; define=define)
end

function _methoddefs!(signatures, stack, frame, pc; define=define)
    while pc !== nothing
        stmt = pc_expr(frame, pc)
        if !ismethod(stmt)
            pc = JuliaInterpreter.next_until!(ismethod, stack, frame, pc, true)
        end
        pc === nothing && break
        ret = methoddef!(signatures, stack, frame, pc; define=define)
        pc = ret === nothing ? ret : ret[1]
    end
    return pc
end

end # module
