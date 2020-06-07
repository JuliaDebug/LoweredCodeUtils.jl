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
        if isanonymous_typedef(stmt)
            lastpc = pc = step_through_methoddef(recurse, frame, stmt)   # define an anonymous function
        elseif isexpr(stmt, :call) && is_quotenode(stmt.args[1], Core.Typeof) &&
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

function minid(@nospecialize(node), stmts, id)
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

function signature_top(frame, stmt::Expr, pc)
    @assert ismethod3(stmt)
    return minid(stmt.args[2], frame.framecode.src.code, pc)
end

function step_through_methoddef(@nospecialize(recurse), frame, @nospecialize(stmt))
    while !isexpr(stmt, :method)
        pc = step_expr!(recurse, frame, stmt, true)
        stmt = pc_expr(frame, pc)
    end
    return step_expr!(recurse, frame, stmt, true)  # also define the method
end

"""
    MethodInfo(start, stop, refs)

Given a frame and its CodeInfo, `start` is the line of the first `Expr(:method, name)`,
whereas `stop` is the line of the last `Expr(:method, name, sig, src)` expression for `name`.
`refs` is a vector of line numbers of other references.
Some of these will be the location of the "declaration" of a method,
the `:thunk` expression containing a CodeInfo that just returns a 1-argument `:method` expression.
Others may be `:global` declarations.

In some cases there may be more than one method with the same name in the `start:stop` range.
"""
mutable struct MethodInfo
    start::Int
    stop::Int
    refs::Vector{Int}
end
MethodInfo(start) = MethodInfo(start, -1, Int[])

"""
    methodinfos, selfcalls = identify_framemethod_calls(frame)

Analyze the code in `frame` to locate method definitions and "self-calls," i.e., calls
to methods defined in `frame` that occur within `frame`.

`methodinfos` is a Dict of `name=>info` pairs, where `info` is a [`MethodInfo`](@ref).

`selfcalls` is a list of `(linetop, linebody, callee, caller)` tuples that holds the location of
calls the methods defined in `frame`. `linetop` is the line in `frame` (top meaning "top level"),
which will correspond to a 3-argument `:method` expression containing a `CodeInfo` body.
`linebody` is the line within the `CodeInfo` body from which the call is made.
`callee` is the Symbol of the called method.
"""
function identify_framemethod_calls(frame)
    refs = Pair{Symbol,Int}[]
    methodinfos = Dict{Symbol,MethodInfo}()
    selfcalls = NamedTuple{(:linetop, :linebody, :callee, :caller),Tuple{Int64,Int64,Symbol,Union{Symbol,Bool}}}[]
    for (i, stmt) in enumerate(frame.framecode.src.code)
        if isexpr(stmt, :global, 1)
            key = stmt.args[1]
            # We don't know for sure if this is a reference to a method, but let's
            # tentatively cue it
            push!(refs, key=>i)
        elseif isexpr(stmt, :thunk, 1) && stmt.args[1] isa CodeInfo
            tsrc = stmt.args[1]::CodeInfo
            if length(tsrc.code) == 1
                tstmt = tsrc.code[1]
                if isexpr(tstmt, :return, 1)
                    tex = tstmt.args[1]
                    if isexpr(tex, :method)
                        push!(refs, tex.args[1]=>i)
                    end
                end
            end
        elseif ismethod1(stmt)
            key = stmt.args[1]::Symbol
            mi = get(methodinfos, key, nothing)
            if mi === nothing
                methodinfos[key] = MethodInfo(i)
            else
                mi.stop == -1 && (mi.start = i) # advance the statement # unless we've seen the method3
            end
        elseif ismethod3(stmt)
            key = stmt.args[1]
            if key isa Symbol
                mi = methodinfos[key]
                mi.stop = i
            elseif key isa Expr   # this is a module-scoped call. We don't have to worry about these because they are named
                continue
            end
            msrc = stmt.args[3]
            if msrc isa CodeInfo
                for (j, mstmt) in enumerate(msrc.code)
                    if isexpr(mstmt, :call)
                        mkey = mstmt.args[1]
                        if isa(mkey, Symbol)
                            # Could be a GlobalRef but then it's outside frame
                            haskey(methodinfos, mkey) && push!(selfcalls, (linetop=i, linebody=j, callee=mkey, caller=key))
                        elseif is_global_ref(mkey, Core, isdefined(Core, :_apply_iterate) ? :_apply_iterate : :_apply)
                            ssaref = mstmt.args[end-1]
                            if isa(ssaref, JuliaInterpreter.SSAValue)
                                id = ssaref.id
                                has_self_call(msrc, msrc.code[id]) || continue
                            end
                            mkey = mstmt.args[end-2]
                            if isa(mkey, Symbol)
                                haskey(methodinfos, mkey) && push!(selfcalls, (linetop=i, linebody=j, callee=mkey, caller=key))
                            end
                        end
                    elseif isexpr(mstmt, :meta) && mstmt.args[1] == :generated
                        newex = mstmt.args[2]
                        if isexpr(newex, :new) && length(newex.args) >= 2 && is_global_ref(newex.args[1], Core, :GeneratedFunctionStub)
                            mkey = newex.args[2]::Symbol
                            haskey(methodinfos, mkey) && push!(selfcalls, (linetop=i, linebody=j, callee=mkey, caller=key))
                        end
                    end
                end
            end
        end
    end
    for r in refs
        mi = get(methodinfos, r.first, nothing)
        mi === nothing || push!(mi.refs, r.second)
    end
    return methodinfos, selfcalls
end

function callchain(selfcalls)
    calledby = Dict{Symbol,Union{Symbol,Bool}}()
    for sc in selfcalls
        startswith(String(sc.callee), '#') || continue
        caller = get(calledby, sc.callee, nothing)
        if caller === nothing
            calledby[sc.callee] = sc.caller
        elseif caller == sc.caller
        else
            error("unexpected multiple callers, ", caller, " and ", sc.caller)
        end
    end
    return calledby
end

function set_to_running_name!(@nospecialize(recurse), replacements, frame, methodinfos, calledby, callee, caller)
    if isa(caller, Symbol) && startswith(String(caller), '#')
        rep = get(replacements, caller, nothing)
        if rep === nothing
            parentcaller = get(calledby, caller, nothing)
            if parentcaller !== nothing
                set_to_running_name!(recurse, replacements, frame, methodinfos, calledby, caller, parentcaller)
            end
        else
            caller = rep
        end
    end
    if isa(caller, Symbol)
        mi = methodinfos[caller]
        cname, _pc, _ = get_running_name(recurse, frame, mi.start, callee, get(replacements, caller, caller))
    else
        # For generated constructors (which have no name), we just assume they immediately follow their callee
        mi = methodinfos[callee]
        cname, _pc, _ = get_running_name(recurse, frame, mi.stop+1, callee, get(replacements, caller, caller))
    end
    replacements[callee] = cname
    mi = methodinfos[cname] = methodinfos[callee]
    src = frame.framecode.src
    replacename!(src.code[mi.start:mi.stop], callee=>cname)        # the method itself
    for r in mi.refs                                               # the references
        replacename!((src.code[r])::Expr, callee=>cname)
    end
    return replacements
end

"""
    methranges = rename_framemethods!(frame)
    methranges = rename_framemethods!(recurse, frame)

Rename the gensymmed methods in `frame` to match those that are currently active.
The issues are described in https://github.com/JuliaLang/julia/issues/30908.
`frame` will be modified in-place as needed.

Returns a vector of `name=>start:stop` pairs specifying the range of lines in `frame`
at which method definitions occur. In some cases there may be more than one method with
the same name in the `start:stop` range.
"""
function rename_framemethods!(@nospecialize(recurse), frame::Frame, methodinfos, selfcalls, calledby)
    src = frame.framecode.src
    replacements = Dict{Symbol,Symbol}()
    for (callee, caller) in calledby
        (!startswith(String(callee), '#') || haskey(replacements, callee)) && continue
        try
            set_to_running_name!(recurse, replacements, frame, methodinfos, calledby, callee, caller)
        catch err
            @warn "skipping callee $callee (called by $caller) due to $err"
        end
    end
    for (linetop, linebody, callee, caller) in selfcalls
        cname = get(replacements, callee, nothing)
        if cname !== nothing && cname !== callee
            replacename!((src.code[linetop].args[3])::CodeInfo, callee=>cname)
        end
    end
    return methodinfos
end

function rename_framemethods!(@nospecialize(recurse), frame::Frame)
    pc0 = frame.pc
    methodinfos, selfcalls = identify_framemethod_calls(frame)
    calledby = callchain(selfcalls)
    rename_framemethods!(recurse, frame, methodinfos, selfcalls, calledby)
    frame.pc = pc0
    return methodinfos
end
rename_framemethods!(frame::Frame) = rename_framemethods!(finish_and_return!, frame)

"""
    pctop, isgen = find_corrected_name(recurse, frame, pc, name, parentname)

Scans forward from `pc` in `frame` until a method is found that calls `name`.
`pctop` points to the beginning of that method's signature.
`isgen` is true if `name` corresponds to sa GeneratedFunctionStub.

Alternatively, this returns `nothing` if `pc` does not appear to point to either
a keyword or generated method.
"""
function find_corrected_name(@nospecialize(recurse), frame, pc, name, parentname)
    stmt = pc_expr(frame, pc)
    while true
        pc0 = pc
        while !ismethod3(stmt)
            pc = next_or_nothing(frame, pc)
            pc === nothing && return nothing
            stmt = pc_expr(frame, pc)
        end
        body = stmt.args[3]
        if stmt.args[1] !== name && isa(body, SSAValue)
            # OK, we can't skip all the stuff that might define the body
            # See https://github.com/timholy/Revise.jl/issues/398
            pc = pc0
            stmt = pc_expr(frame, pc)
            while !ismethod3(stmt)
                pc = step_expr!(recurse, frame, stmt, true)
                pc === nothing && return nothing
                stmt = pc_expr(frame, pc)
            end
            body = @lookup(frame, stmt.args[3])
        end
        if stmt.args[1] !== name && isa(body, CodeInfo)
            # This might be the GeneratedFunctionStub for a @generated method
            for (i, bodystmt) in enumerate(body.code)
                if isexpr(bodystmt, :meta) && bodystmt.args[1] === :generated
                    return signature_top(frame, stmt, pc), true
                end
                i >= 5 && break  # we should find this early
            end
            if length(body.code) > 1
                bodystmt = body.code[end-1]  # the line before the final return
                iscallto(bodystmt, name) && return signature_top(frame, stmt, pc), false
            end
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

replacename!(src::CodeInfo, pr) = replacename!(src.code, pr)

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
        elseif isa(a, Vector{Any})
            replacename!(a, pr)
        elseif a == oldname
            args[i] = newname
        end
    end
    return args
end

function get_running_name(@nospecialize(recurse), frame, pc, name, parentname)
    # Get the correct name (the one that's actively running)
    nameinfo = find_corrected_name(recurse, frame, pc, name, parentname)
    if nameinfo === nothing
        pc = skip_until(stmt->isexpr(stmt, :method, 3), frame, pc)
        pc = next_or_nothing(frame, pc)
        return name, pc, nothing
    end
    pctop, isgen = nameinfo
    # Sometimes signature_top---which follows SSAValue links backwards to find the first
    # line needed to define the signature---misses out on a SlotNumber assignment.
    # Fix https://github.com/timholy/Revise.jl/issues/422
    stmt = pc_expr(frame, pctop)
    while pctop > 1 && isa(stmt, SlotNumber) && !isassigned(frame.framedata.locals, pctop)
        pctop -= 1
        stmt = pc_expr(frame, pctop)
    end   # end fix
    sigtparent, lastpcparent = signature(recurse, frame, pctop)
    sigtparent === nothing && return name, pc, lastpcparent
    methparent = whichtt(sigtparent)
    methparent === nothing && return name, pc, lastpcparent  # caller isn't defined, no correction is needed
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
    return cname, pc, lastpcparent
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
"""
function methoddef!(@nospecialize(recurse), signatures, frame::Frame, @nospecialize(stmt), pc::Int; define::Bool=true)
    framecode, pcin = frame.framecode, pc
    if ismethod3(stmt)
        pc3 = pc
        sigt, pc = signature(recurse, frame, stmt, pc)
        if sigt === nothing && define
            step_expr!(recurse, frame, stmt, true)
        end
        sigt, pc = signature(recurse, frame, stmt, pc)
        meth = whichtt(sigt)
        if (meth === nothing || !(meth.sig <: sigt && sigt <: meth.sig)) && define
            step_expr!(recurse, frame, stmt, true)
            meth = whichtt(sigt)
        end
        if isa(meth, Method)
            push!(signatures, meth.sig)
        elseif stmt.args[1] === false
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
    name = name::Symbol
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
        name === name3 && return pc, pc3     # if this was an inner method we should keep going
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

function is_self_call(@nospecialize(stmt), slotnames, argno=1)
    if isa(stmt, Expr)
        if stmt.head == :call
            a = stmt.args[argno]
            if isa(a, SlotNumber) || isa(a, Core.SlotNumber)
                sn = slotnames[a.id]
                if sn == Symbol("#self#") || sn == Symbol("") # allow empty to fix https://github.com/timholy/CodeTracking.jl/pull/48
                    return true
                end
            end
        end
    end
    return false
end

function has_self_call(src, stmt::Expr)
    # Check that it has a #self# call
    hasself = false
    for i = 2:length(stmt.args)
        hasself |= is_self_call(stmt, src.slotnames, i)
    end
    return hasself
end

"""
    mbody = bodymethod(m::Method)

Return the "body method" for a method `m`. `mbody` contains the code of the function body
when `m` was defined.
"""
function bodymethod(mkw::Method)
    m = mkw
    local src
    while true
        framecode = JuliaInterpreter.get_framecode(m)
        fakeargs = Any[nothing for i = 1:framecode.scope.nargs]
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
        if f.value === (isdefined(Core, :_apply_iterate) ? Core._apply_iterate : Core._apply)
            ssaref = stmt.args[end-1]
            if isa(ssaref, JuliaInterpreter.SSAValue)
                id = ssaref.id
                has_self_call(src, src.code[id]) || return m
            end
            f = stmt.args[end-2]
        else
            has_self_call(src, stmt) || return m
        end
        f = f.value
        mths = methods(f)
        if length(mths) == 1
            return first(mths)
        end
    end
    return m
end
