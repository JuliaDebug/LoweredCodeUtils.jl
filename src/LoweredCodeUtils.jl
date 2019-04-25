module LoweredCodeUtils

using Core: SimpleVector, CodeInfo
using Base.Meta: isexpr
using JuliaInterpreter
using JuliaInterpreter: SSAValue, SlotNumber, Frame
using JuliaInterpreter: @lookup, moduleof, pc_expr, step_expr!, is_global_ref, whichtt,
                        next_until!, finish_and_return!, nstatements, codelocation

export signature, methoddef!, methoddefs!, bodymethod

"""
    iscallto(stmt, name)

Returns `true` is `stmt` is a call expression to `name`.
"""
function iscallto(stmt, name)
    if isexpr(stmt, :call)
        a = stmt.args[1]
        a == name && return true
        return is_global_ref(a, Core, :_apply) && stmt.args[2] == name
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
        is_global_ref(a, Core, :_apply) && return stmt.args[2]
        return a
    end
    error(stmt, " is not a call expression")
end

ismethod(frame::Frame) = ismethod(pc_expr(frame))
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
    sigt, lastpc = signature(recurse, frame, pc)
    sigt, lastpc = signature(frame, pc)

Compute the signature-type `sigt` of a method whose definition in `frame` starts at `pc`.
Generally, `pc` should point to the `Expr(:method, methname)` statement, in which case
`lastpc` is the final statement number in `frame` that is part of the signature
(i.e, the line above the 3-argument `:method` expression).
Alternatively, `pc` can point to the 3-argument `:method` expression,
as long as all the relevant SSAValues have been assigned.
In this case, `lastpc == pc`.

If no 3-argument `:method` expression is found, `sigt` will be `nothing`.
"""
function signature(@nospecialize(recurse), frame::Frame, @nospecialize(stmt), pc)
    mod = moduleof(frame)
    lastpc = frame.pc = pc
    while !isexpr(stmt, :method, 3)  # wait for the 3-arg version
        if isexpr(stmt, :thunk) && isanonymous_typedef(stmt.args[1])
            lastpc = pc = define_anonymous(recurse, frame, stmt)
        elseif isexpr(stmt, :call) && JuliaInterpreter.is_quotenode(stmt.args[1], Core.Typeof) &&
               (sym = stmt.args[2]; isa(sym, Symbol) && !isdefined(mod, sym))
            return nothing, pc
        else
            lastpc = pc
            pc = step_expr!(recurse, frame, stmt, true)
            pc === nothing && return nothing, lastpc
        end
        stmt = pc_expr(frame, pc)
    end
    sigsv = @lookup(frame, stmt.args[2])::SimpleVector
    sigt = signature(sigsv)
    return sigt, lastpc
end
signature(@nospecialize(recurse), frame::Frame, pc) = signature(recurse, frame, pc_expr(frame, pc), pc)
signature(frame::Frame, pc) = signature(finish_and_return!, frame, pc)

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
    return minid(stmt.args[2], frame.framecode.src.code, pc)
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

function define_anonymous(@nospecialize(recurse), frame, stmt)
    while !isexpr(stmt, :method)
        pc = step_expr!(recurse, frame, stmt, true)
        stmt = pc_expr(frame, pc)
    end
    return step_expr!(recurse, frame, stmt, true)  # also define the method
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

function correct_name!(@nospecialize(recurse), frame, pc, name, parentname)
    # Get the correct name (the one that's actively running)
    nameinfo = find_corrected_name(frame, pc, name, parentname)
    if nameinfo === nothing
        pc = skip_until(stmt->isexpr(stmt, :method, 3), frame, pc)
        pc = next_or_nothing(frame, pc)
        return name, pc
    end
    pctop, isgen = nameinfo
    sigtparent, lastpcparent = signature(recurse, frame, pctop)
    sigtparent === nothing && return name, pc
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
        replacename!(frame.framecode.src.code, name=>cname)
    end
    stmt = pc_expr(frame, lastpcparent)
    while !ismethod(stmt)
        lastpcparent = next_or_nothing(frame, lastpcparent)
        lastpcparent === nothing && return name, lastpcparent
        stmt = pc_expr(frame, lastpcparent)
    end
    name = stmt.args[1]
    return name, pc
end

"""
    ret = methoddef!(recurse, signatures, frame; define=true)
    ret = methoddef!(signatures, frame; define=true)

Compute the signature of a method definition. `frame.pc` should point to a
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
function methoddef!(@nospecialize(recurse), signatures, frame::Frame, @nospecialize(stmt), pc::Int; define=true)
    framecode = frame.framecode
    if ismethod3(stmt)
        pc3 = pc
        sigt, pc = signature(recurse, frame, stmt, pc)
        if sigt === nothing && define
            step_expr!(recurse, frame, stmt, true)
        end
        sigt, pc = signature(recurse, frame, stmt, pc)
        meth = whichtt(sigt)
        if meth === nothing && define
            step_expr!(recurse, frame, stmt, true)
            meth = whichtt(sigt)
        end
        if isa(meth, Method)
            push!(signatures, meth.sig)
        elseif stmt.args[1] == false
            # If it's anonymous and not defined, define it
            pc = step_expr!(recurse, frame, stmt, true)
            meth = whichtt(sigt)
            isa(meth, Method) && push!(signatures, meth.sig)
            return pc, pc3
        else
            # guard against busted lookup, e.g., https://github.com/JuliaLang/julia/issues/31112
            code = framecode.src
            codeloc = codelocation(code, pc)
            loc = code.linetable[codeloc]
            ft = Base.unwrap_unionall(Base.unwrap_unionall(sigt).parameters[1])
            if !startswith(String(ft.name.name), "##")
                @warn "file $(loc.file), line $(loc.line): no method found for $sigt"
            end
        end
        frame.pc = pc
        return ( define ? step_expr!(recurse, frame, stmt, true) : next_or_nothing!(frame) ), pc3
    end
    ismethod1(stmt) || error("expected method opening, got ", stmt)
    name = stmt.args[1]
    if isa(name, Bool)
        error("not valid for anonymous methods")
    end
    parentname = get_parentname(name)  # e.g., name = #foo#7 and parentname = foo
    pcinc = 1
    nextstmt = pc_expr(frame, pc+pcinc)
    while ismethod1(nextstmt) || isexpr(nextstmt, :global)
        if ismethod1(nextstmt)
            name = nextstmt.args[1]
        end
        pcinc += 1
        nextstmt = pc_expr(frame, pc+pcinc)
    end
    if !define && String(name)[1] == '#'
        # We will have to correct the name.
        # We can only correct one at a time, so work backwards from a non-gensymmed name
        # (https://github.com/timholy/Revise.jl/issues/290)
        pc0 = pc
        idx1 = findall(ismethod1, frame.framecode.src.code)
        idx1 = idx1[idx1 .>= pc]
        hashhash = map(idx->startswith(String(pc_expr(frame, idx).args[1]), '#'), idx1)
        idx1 = idx1[hashhash]
        i = length(idx1)
        while i > 1
            frame.pc = idx1[i]
            methoddef!(recurse, [], frame, frame.pc; define=define)
            i -= 1
        end
        frame.pc = pc0
    end
    if name != parentname && !define
        name, endpc = correct_name!(recurse, frame, pc, name, parentname)
    end
    while true  # methods containing inner methods may need multiple trips through this loop
        sigt, pc = signature(recurse, frame, stmt, pc)
        stmt = pc_expr(frame, pc)
        while !isexpr(stmt, :method, 3)
            pc = next_or_nothing(frame, pc)  # this should not check define, we've probably already done this once
            pc === nothing && return nothing   # this was just `function foo end`, signal "no def"
            stmt = pc_expr(frame, pc)
        end
        pc3 = pc
        name3 = stmt.args[1]
        sigt === nothing && (error("expected a signature"); return next_or_nothing(frame, pc)), pc3
        # Methods like f(x::Ref{<:Real}) that use gensymmed typevars will not have the *exact*
        # signature of the active method. So let's get the active signature.
        frame.pc = pc
        pc = define ? step_expr!(recurse, frame, stmt, true) : next_or_nothing!(frame)
        meth = whichtt(sigt)
        isa(meth, Method) && push!(signatures, meth.sig) # inner methods are not visible
        name == name3 && return pc, pc3     # if this was an inner method we should keep going
        stmt = pc_expr(frame, pc)  # there *should* be more statements in this frame
    end
end
methoddef!(@nospecialize(recurse), signatures, frame::Frame, pc::Int; define=true) =
    methoddef!(recurse, signatures, frame, pc_expr(frame, pc), pc; define=define)
function methoddef!(@nospecialize(recurse), signatures, frame::Frame; define=true)
    pc = frame.pc
    stmt = pc_expr(frame, pc)
    if !ismethod(stmt)
        pc = next_until!(ismethod, recurse, frame, true)
    end
    pc === nothing && error("pc at end of frame without finding a method")
    methoddef!(recurse, signatures, frame, pc; define=define)
end
methoddef!(signatures, frame::Frame; define=true) =
    methoddef!(finish_and_return!, signatures, frame; define=define)

function methoddefs!(@nospecialize(recurse), signatures, frame::Frame, pc; define=true)
    ret = methoddef!(recurse, signatures, frame, pc; define=define)
    pc = ret === nothing ? ret : ret[1]
    return _methoddefs!(recurse, signatures, frame, pc; define=define)
end
function methoddefs!(@nospecialize(recurse), signatures, frame::Frame; define=true)
    ret = methoddef!(recurse, signatures, frame; define=define)
    pc = ret === nothing ? ret : ret[1]
    return _methoddefs!(recurse, signatures, frame, pc; define=define)
end
methoddefs!(signatures, frame::Frame; define=true) =
    methoddefs!(finish_and_return!, signatures, frame; define=define)

function _methoddefs!(@nospecialize(recurse), signatures, frame::Frame, pc; define=define)
    while pc !== nothing
        stmt = pc_expr(frame, pc)
        if !ismethod(stmt)
            pc = next_until!(ismethod, recurse, frame, true)
        end
        pc === nothing && break
        ret = methoddef!(recurse, signatures, frame, pc; define=define)
        pc = ret === nothing ? ret : ret[1]
    end
    return pc
end

"""
    mbody = bodymethod(m::Method)

Return the "body method" for a method `m`. `mbody` contains the code of the function body
when `m` was defined.
"""
function bodymethod(mkw::Method)
    function is_self_call(stmt, slotnames, argno=1)
        if isa(stmt, Expr)
            if stmt.head == :call
                a = stmt.args[argno]
                if isa(a, SlotNumber)
                    if slotnames[a.id] == Symbol("#self#")
                        return true
                    end
                end
            end
        end
        return false
    end
    m = mkw
    local src
    while true
        framecode = JuliaInterpreter.get_framecode(m)
        fakeargs = Any[nothing for i = 1:length(framecode.scope.nargs)]
        frame = JuliaInterpreter.prepare_frame(framecode, fakeargs, isa(m.sig, UnionAll) ? sparam_ub(m) : Core.svec())
        src = framecode.src
        (length(src.code) > 1 && is_self_call(src.code[end-1], src.slotnames)) || break
        # Build the optional arg, so we can get its type
        pc = frame.pc
        while pc < length(src.code) - 1
            pc = step_expr!(frame)
        end
        val = pc > 1 ? frame.framedata.ssavalues[pc-1] : src.code[1].args[end]
        sig = Tuple{Base.unwrap_unionall(m.sig).parameters..., typeof(val)}
        m = whichtt(sig)
    end
    length(src.code) > 1 || return m
    stmt = src.code[end-1]
    if isexpr(stmt, :call) && (f = stmt.args[1]; isa(f, QuoteNode))
        # Check that it has a #self# call
        hasself = any(i->is_self_call(stmt, src.slotnames, i), 1:length(stmt.args))
        hasself || return m
        f = f.value
        mths = methods(f)
        if length(mths) == 1
            return first(mths)
        end
    end
    return m
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

# precompilation

if ccall(:jl_generating_output, Cint, ()) == 1
    kwdefine = NamedTuple{(:define,),Tuple{Bool}}
    for ct in (Vector{Any}, Set{Any})
        f = methoddef!
        precompile(Tuple{typeof(f), ct, Any, Frame, Expr, Int})
        precompile(Tuple{Core.kwftype(typeof(f)), kwdefine, typeof(f), ct, Any, Frame, Expr, Int})
        f = methoddefs!
        precompile(Tuple{typeof(f), ct, Any, Frame})
        precompile(Tuple{Core.kwftype(typeof(f)), kwdefine, typeof(f), ct, Any, Frame})
    end
    precompile(Tuple{typeof(get_parentname), Symbol})
    precompile(Tuple{typeof(correct_name!), Any, Frame, Int, Symbol, Symbol})
end

end # module
