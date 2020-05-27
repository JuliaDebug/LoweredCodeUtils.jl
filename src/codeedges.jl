const NamedVar = Union{Symbol,GlobalRef}

## Phase 1: direct links

# There are 3 types of entities to track: ssavalues (line/statement numbers), slots, and named objects.
# Each entity can have a number of "predecessors" (forward edges), which can be any combination of these
# three entity types. Likewise, each entity can have a number of "successors" (backward edges), also any
# combination of these entity types.
struct Links
    ssas::Vector{Int}
    slots::Vector{Int}
    names::Vector{NamedVar}
end
Links() = Links(Int[], Int[], Int[])

function Base.show(io::IO, l::Links)
    print(io, "ssas: ", showempty(l.ssas),
              ", slots: ", showempty(l.slots),
              ", names: ")
    print(IOContext(io, :typeinfo=>Vector{NamedVar}), showempty(l.names))
    print(io, ';')
end

struct CodeLinks
    ssapreds::Vector{Links}
    ssasuccs::Vector{Links}
    slotpreds::Vector{Links}
    slotsuccs::Vector{Links}
    slotassigns::Vector{Vector{Int}}
    namepreds::Dict{NamedVar,Links}
    namesuccs::Dict{NamedVar,Links}
    nameassigns::Dict{NamedVar,Vector{Int}}
end
function CodeLinks(nlines::Int, nslots::Int)
    return CodeLinks([Links() for _ = 1:nlines],
                     [Links() for _ = 1:nlines],
                     [Links() for _ = 1:nslots],
                     [Links() for _ = 1:nslots],
                     [Int[] for _ = 1:nslots],
                     Dict{NamedVar,Links}(),
                     Dict{NamedVar,Links}(),
                     Dict{NamedVar,Vector{Int}}())
end
function CodeLinks(src::CodeInfo)
    cl = CodeLinks(length(src.code), length(src.slotnames))
    direct_links!(cl, src)
end

function Base.show(io::IO, cl::CodeLinks)
    print(io, "CodeLinks:")
    print_slots(io, cl)
    print_names(io, cl)
    nstmts = length(cl.ssapreds)
    nd = ndigits(nstmts)
    print(io, "\nCode:")
    for i = 1:nstmts
        print(io, '\n', lpad(i, nd), " preds: ")
        show(io, cl.ssapreds[i])
        print(io, '\n', lpad(i, nd), " succs: ")
        show(io, cl.ssasuccs[i])
    end
end

function print_slots(io::IO, cl::CodeLinks)
    nslots = length(cl.slotpreds)
    nd = ndigits(nslots)
    for i = 1:nslots
        print(io, "\nslot ", lpad(i, nd), ':')
        print(io, "\n  preds: ")
        show(io, cl.slotpreds[i])
        print(io, "\n  succs: ")
        show(io, cl.slotsuccs[i])
        print(io, "\n  assign @: ")
        show(io, cl.slotassigns[i])
    end
end

function print_names(io::IO, cl::CodeLinks)
    ukeys = namedkeys(cl)
    for key in ukeys
        print(io, '\n', key, ':')
        if haskey(cl.namepreds, key)
            print(io, "\n  preds: ")
            show(io, cl.namepreds[key])
        end
        if haskey(cl.namesuccs, key)
            print(io, "\n  succs: ")
            show(io, cl.namesuccs[key])
        end
        if haskey(cl.nameassigns, key)
            print(io, "\n  assign @: ")
            show(io, cl.nameassigns[key])
        end
    end
end

if isdefined(Base.IRShow, :show_ir_stmt)
    function print_with_code(preprint, postprint, io::IO, src::CodeInfo)
        src = JuliaInterpreter.copy_codeinfo(src)
        JuliaInterpreter.replace_coretypes!(src; rev=true)
        if isdefined(JuliaInterpreter, :reverse_lookup_globalref!)
            JuliaInterpreter.reverse_lookup_globalref!(src.code)
        end
        io = IOContext(io, :displaysize=>displaysize(io))
        used = BitSet()
        cfg = Core.Compiler.compute_basic_blocks(src.code)
        for stmt in src.code
            Core.Compiler.scan_ssa_use!(push!, used, stmt)
        end
        line_info_preprinter = Base.IRShow.lineinfo_disabled
        line_info_postprinter = Base.IRShow.default_expr_type_printer
        preprint(io)
        bb_idx_prev = bb_idx = 1
        for idx = 1:length(src.code)
            preprint(io, idx)
            bb_idx = Base.IRShow.show_ir_stmt(io, src, idx, line_info_preprinter, line_info_postprinter, used, cfg, bb_idx)
            postprint(io, idx, bb_idx != bb_idx_prev)
            bb_idx_prev = bb_idx
        end
        max_bb_idx_size = ndigits(length(cfg.blocks))
        line_info_preprinter(io, " "^(max_bb_idx_size + 2), typemin(Int32))
        postprint(io)
        return nothing
    end
else
    function print_with_code(preprint, postprint, io::IO, src::CodeInfo)
        println(io, "No IR statement printer available on this version of Julia, just aligning statements.")
        preprint(io)
        for idx = 1:length(src.code)
            preprint(io, idx)
            print(io, src.code[idx])
            println(io)
            postprint(io, idx, false)
        end
        postprint(io)
    end
end

"""
    print_with_code(io, src::CodeInfo, cl::CodeLinks)

Interweave display of code and links.

!!! compat Julia 1.6
    This function produces dummy output if suitable support is missing in your version of Julia.
"""
function print_with_code(io::IO, src::CodeInfo, cl::CodeLinks)
    function preprint(io::IO)
        print(io, "Slots:")
        print_slots(io, cl)
        print(io, "\nNames:")
        print_names(io, cl)
        println(io)
    end
    preprint(::IO, ::Int) = nothing
    postprint(::IO) = nothing
    postprint(io::IO, idx::Int, bbchanged::Bool) = postprint_linelinks(io, idx, src, cl, bbchanged)

    print_with_code(preprint, postprint, io, src)
end

function postprint_linelinks(io::IO, idx::Int, src::CodeInfo, cl::CodeLinks, bbchanged::Bool)
    printstyled(io, bbchanged ? " " : "│", color=:light_black)
    printstyled(io, "             # ", color=:yellow)
    stmt = src.code[idx]
    if isexpr(stmt, :(=))
        lhs = stmt.args[1]
        if isslotnum(lhs)
            # id = lhs.id
            # preds, succs = cl.slotpreds[id], cl.slotsuccs[id]
            printstyled(io, "see slot ", lhs.id, '\n', color=:yellow)
        else
            # preds, succs = cl.namepreds[lhs], cl.namesuccs[lhs]
            printstyled(io, "see name ", lhs, '\n', color=:yellow)
        end
    else
        preds, succs = cl.ssapreds[idx], cl.ssasuccs[idx]
        printstyled(io, "preds: ", preds, " succs: ", succs, '\n', color=:yellow)
    end
    return nothing
end


function namedkeys(cl::CodeLinks)
    ukeys = Set{NamedVar}()
    for c in (cl.namepreds, cl.namesuccs, cl.nameassigns)
        for k in keys(c)
            push!(ukeys, k)
        end
    end
    return ukeys
end

function direct_links!(cl::CodeLinks, src::CodeInfo)
    for (i, stmt) in enumerate(src.code)
        if isexpr(stmt, :thunk) && isa(stmt.args[1], CodeInfo)
            icl = CodeLinks(stmt.args[1])
            for (name, _) in icl.nameassigns
                assign = get(cl.nameassigns, name, nothing)
                if assign === nothing
                    cl.nameassigns[name] = assign = Int[]
                end
                push!(assign, i)
            end
            continue
        elseif isa(stmt, Expr) && stmt.head ∈ trackedheads
            name = stmt.args[1]
            if isa(name, Symbol)
                assign = get(cl.nameassigns, name, nothing)
                if assign === nothing
                    cl.nameassigns[name] = assign = Int[]
                end
                push!(assign, i)
                targetstore = get(cl.namepreds, name, nothing)
                if targetstore === nothing
                    cl.namepreds[name] = targetstore = Links()
                end
                target = name=>targetstore
                add_links!(target, stmt, cl)
            end
            rhs = stmt
            target = SSAValue(i)=>cl.ssapreds[i]
        elseif isexpr(stmt, :(=))
            # An assignment
            stmt = stmt::Expr
            lhs, rhs = stmt.args[1], stmt.args[2]
            if isslotnum(lhs)
                lhs = lhs::AnySlotNumber
                id = lhs.id
                target = SlotNumber(id)=>cl.slotpreds[id]
                push!(cl.slotassigns[id], i)
            elseif isa(lhs, NamedVar)
                targetstore = get(cl.namepreds, lhs, nothing)
                if targetstore === nothing
                    cl.namepreds[lhs] = targetstore = Links()
                end
                target = lhs=>targetstore
                assign = get(cl.nameassigns, lhs, nothing)
                if assign === nothing
                    cl.nameassigns[lhs] = assign = Int[]
                end
                push!(assign, i)
            else
                error("lhs ", lhs, " not recognized")
            end
        else
            rhs = stmt
            target = SSAValue(i)=>cl.ssapreds[i]
        end
        add_links!(target, rhs, cl)
    end
    return cl
end

function add_links!(target::Pair{<:Any,Links}, @nospecialize(stmt), cl::CodeLinks)
    targetid, targetstore = target
    # Adds bidirectional edges
    if isssa(stmt)
        push!(targetstore, stmt)                 # forward edge
        push!(cl.ssasuccs[stmt.id], targetid)    # backward edge
    elseif isslotnum(stmt)
        push!(targetstore, stmt)
        push!(cl.slotsuccs[stmt.id], targetid)
    elseif isa(stmt, NamedVar)
        push!(targetstore, stmt)
        namestore = get(cl.namesuccs, stmt, nothing)
        if namestore === nothing
            cl.namesuccs[stmt] = namestore = Links()
        end
        push!(namestore, targetid)
    elseif isa(stmt, Expr)
        arng = 1:length(stmt.args)
        if stmt.head === :call
            f = stmt.args[1]
            if !isssa(f) && !isslotnum(f)
                # Avoid putting named callees on the namestore
                arng = 2:length(stmt.args)
            end
        end
        for i in arng
            add_links!(target, stmt.args[i], cl)
        end
    elseif isa(stmt, QuoteNode)
        add_links!(target, stmt.value, cl)
    end
    return nothing
end

function Base.push!(l::Links, id)
    if isssa(id)
        k = id.id
        k ∉ l.ssas && push!(l.ssas, k)
    elseif isslotnum(id)
        k = id.id
        k ∉ l.slots && push!(l.slots, k)
    else
        # NamedVar
        id ∉ l.names && push!(l.names, id)
    end
    return id
end

## Phase 2: replacing slot-links with statement-links (and adding name-links to statement-links)

# Now that we know the full set of dependencies, we can safely replace references to names
# by references to the relevant line numbers.

"""
`Variable` holds information about named variables.
Unlike SSAValues, a single Variable can be assigned from multiple code locations.

If `v` is a `Variable`, then
- `v.assigned` is a list of statement numbers on which it is assigned
- `v.preds` is the set of statement numbers upon which this assignment depends
- `v.succs` is the set of statement numbers which make use of this variable

`preds` and `succs` are short for "predecessors" and "successors," respectively.
These are meant in the sense of execution order, not statement number; depending on control-flow,
a variable may have entries in `preds` that are larger than the smallest entry in `assigned`.
"""
struct Variable
    assigned::Vector{Int}
    preds::Vector{Int}
    succs::Vector{Int}
end
Variable() = Variable(Int[], Int[], Int[])

function Base.show(io::IO, v::Variable)
    print(io, "assigned on ", showempty(v.assigned))
    print(io, ", depends on ", showempty(v.preds))
    print(io, ", and used by ", showempty(v.succs))
end

# This will be documented below at the "user-level" constructor.
# preds[i] is the list of predecessors for the `i`th statement in the CodeInfo
# succs[i] is the list of successors for the `i`th statement in the CodeInfo
# byname[name] summarizes this CodeInfo's dependence on Variable `name`.
struct CodeEdges
    preds::Vector{Vector{Int}}
    succs::Vector{Vector{Int}}
    byname::Dict{NamedVar,Variable}
end
CodeEdges(n::Integer) = CodeEdges([Int[] for i = 1:n], [Int[] for i = 1:n], Dict{Union{GlobalRef,Symbol},Variable}())

function Base.show(io::IO, edges::CodeEdges)
    println(io, "CodeEdges:")
    for (name, v) in edges.byname
        print(io, "  ", name, ": ")
        show(io, v)
        println(io)
    end
    n = length(edges.preds)
    nd = ndigits(n)
    for i = 1:n
        println(io, "  statement ", lpad(i, nd), " depends on ", showempty(edges.preds[i]), " and is used by ", showempty(edges.succs[i]))
    end
    return nothing
end


"""
    edges = CodeEdges(src::CodeInfo)

Analyze `src` and determine the chain of dependencies.

- `edges.preds[i]` lists the preceding statements that statement `i` depends on.
- `edges.succs[i]` lists the succeeding statements that depend on statement `i`.
- `edges.byname[v]` returns information about the predecessors, successors, and assignment statements
  for an object `v::Union{Symbol,GlobalRef}`.
"""
function CodeEdges(src::CodeInfo)
    src.inferred && error("supply lowered but not inferred code")
    cl = CodeLinks(src)
    CodeEdges(src, cl)
end

function CodeEdges(src::CodeInfo, cl::CodeLinks)
    function pushall!(dest, src)
        for item in src
            push!(dest, item)
        end
        return dest
    end
    # The main task here is to elide the slot-dependencies and convert
    # everything to just ssas & names.
    # Hence we "follow" slot links to their non-slot leaves.
    function follow_links!(marked, l::Links, slotlinks, slotassigns, slothandled)
        pushall!(marked, l.ssas)
        for id in l.slots
            slothandled[id] && continue
            slothandled[id] = true
            pushall!(marked, slotassigns[id])
            follow_links!(marked, slotlinks[id], slotlinks, slotassigns, slothandled)
        end
        return marked
    end

    # Replace/add named intermediates (slot & named-variable references) with statement numbers
    nstmts, nslots = length(src.code), length(src.slotnames)
    marked, slothandled = BitSet(), fill(false, nslots)  # working storage during resolution
    edges = CodeEdges(nstmts)
    emptylink = Links()
    emptylist = Int[]
    for (i, stmt) in enumerate(src.code)
        # Identify line predecents for slots and named variables
        if isexpr(stmt, :(=))
            stmt = stmt::Expr
            lhs = stmt.args[1]
            # Mark predecessors and successors of this line by following ssas & named assignments
            if isslotnum(lhs)
                lhs = lhs::AnySlotNumber
                # This line assigns a slot. Mark all predecessors.
                id = lhs.id
                linkpreds, linksuccs, listassigns = cl.slotpreds[id], cl.slotsuccs[id], cl.slotassigns[id]
            else
                lhs = lhs::NamedVar
                linkpreds = get(cl.namepreds, lhs, emptylink)
                linksuccs = get(cl.namesuccs, lhs, emptylink)
                listassigns = get(cl.nameassigns, lhs, emptylist)
            end
        else
            linkpreds, linksuccs, listassigns = cl.ssapreds[i], cl.ssasuccs[i], emptylist
        end
        # Assign the predecessors
        # For "named" predecessors, we depend only on their assignments
        empty!(marked)
        fill!(slothandled, false)
        follow_links!(marked, linkpreds, cl.slotpreds, cl.slotassigns, slothandled)
        pushall!(marked, listassigns)
        for key in linkpreds.names
            pushall!(marked, get(cl.nameassigns, key, emptylist))
        end
        delete!(marked, i)
        append!(edges.preds[i], marked)
        # Similarly for successors
        empty!(marked)
        fill!(slothandled, false)
        follow_links!(marked, linksuccs, cl.slotsuccs, cl.slotassigns, slothandled)
        pushall!(marked, listassigns)
        for key in linksuccs.names
            pushall!(marked, get(cl.nameassigns, key, emptylist))
        end
        delete!(marked, i)
        append!(edges.succs[i], marked)
    end
    # Add named variables
    ukeys = namedkeys(cl)
    for key in ukeys
        assigned = get(cl.nameassigns, key, Int[])
        empty!(marked)
        linkpreds = get(cl.namepreds, key, emptylink)
        pushall!(marked, linkpreds.ssas)
        for j in linkpreds.slots
            pushall!(marked, cl.slotassigns[j])
        end
        for key in linkpreds.names
            pushall!(marked, get(cl.nameassigns, key, emptylist))
        end
        preds = append!(Int[], marked)
        empty!(marked)
        linksuccs = get(cl.namesuccs, key, emptylink)
        pushall!(marked, linksuccs.ssas)
        for j in linksuccs.slots
            pushall!(marked, cl.slotassigns[j])
            pushall!(marked, cl.slotsuccs[j].ssas)
        end
        for key in linksuccs.names
            pushall!(marked, get(cl.nameassigns, key, emptylist))
        end
        succs = append!(Int[], marked)
        edges.byname[key] = Variable(assigned, preds, succs)
    end

    return edges
end

"""
    print_with_code(io, src::CodeInfo, edges::CodeEdges)

Interweave display of code and edges.

!!! compat Julia 1.6
    This function produces dummy output if suitable support is missing in your version of Julia.
"""
function print_with_code(io::IO, src::CodeInfo, edges::CodeEdges)
    function preprint(io::IO)
        printstyled(io, "Names:", color=:yellow)
        for (name, var) in edges.byname
            print(io, '\n', name, ": ")
            show(io, var)
        end
        printstyled(io, "\nCode:\n", color=:yellow)
    end
    @static if isdefined(Base.IRShow, :show_ir_stmt)
        preprint(::IO, ::Int) = nothing
    else
        nd = ndigits(length(src.code))
        preprint(io::IO, i::Int) = print(io, lpad(i, nd), "  ")
    end
    postprint(::IO) = nothing
    postprint(io::IO, idx::Int, bbchanged::Bool) = postprint_lineedges(io, idx, edges, bbchanged)

    print_with_code(preprint, postprint, io, src)
end

function postprint_lineedges(io::IO, idx::Int, edges::CodeEdges, bbchanged::Bool)
    printstyled(io, bbchanged ? " " : "│", color=:light_black)
    printstyled(io, "             # ", color=:yellow)
    preds, succs = edges.preds[idx], edges.succs[idx]
    printstyled(io, "preds: ", showempty(preds), ", succs: ", showempty(succs), '\n', color=:yellow)
    return nothing
end


"""
    isrequired = lines_required(obj::Union{Symbol,GlobalRef}, src::CodeInfo, edges::CodeEdges)
    isrequired = lines_required(idx::Int,                     src::CodeInfo, edges::CodeEdges)

Determine which lines might need to be executed to evaluate `obj` or the statement indexed by `idx`.
If `isrequired[i]` is `false`, the `i`th statement is *not* required.
In some circumstances all statements marked `true` may be needed, in others control-flow
will end up skipping a subset of such statements, perhaps while repeating others multiple times.

See also [`lines_required!`](@ref) and [`selective_eval!`](@ref).
"""
function lines_required(obj::Union{Symbol,GlobalRef}, src::CodeInfo, edges::CodeEdges)
    isrequired = falses(length(edges.preds))
    objs = Set{Union{Symbol,GlobalRef}}([obj])
    return lines_required!(isrequired, objs, src, edges)
end

function lines_required(idx::Int, src::CodeInfo, edges::CodeEdges)
    isrequired = falses(length(edges.preds))
    isrequired[idx] = true
    objs = Set{Union{Symbol,GlobalRef}}()
    return lines_required!(isrequired, src, edges)
end

"""
    lines_required!(isrequired::AbstractVector{Bool}, src::CodeInfo, edges::CodeEdges)

Like `lines_required`, but where `isrequired[idx]` has already been set to `true` for all statements
that you know you need to evaluate. All other statements should be marked `false` at entry.
On return, the complete set of required statements will be marked `true`.
"""
function lines_required!(isrequired::AbstractVector{Bool}, src::CodeInfo, edges::CodeEdges)
    objs = Set{Union{Symbol,GlobalRef}}()
    return lines_required!(isrequired, objs, src, edges)
end

function lines_required!(isrequired::AbstractVector{Bool}, objs, src::CodeInfo, edges::CodeEdges)
    # Do a traveral of "numbered" predecessors
    function add_preds!(isrequired, idx, edges::CodeEdges)
        preds = edges.preds[idx]
        for p in preds
            isrequired[p] && continue
            isrequired[p] = true
            add_preds!(isrequired, p, edges)
        end
        return isrequired
    end
    function add_succs!(isrequired, idx, edges::CodeEdges, succs)
        for p in succs
            isrequired[p] && continue
            isrequired[p] = true
            add_succs!(isrequired, p, edges, edges.succs[p])
        end
        return isrequired
    end

    bbs = Core.Compiler.compute_basic_blocks(src.code)  # needed for control-flow analysis
    changed = true
    iter = 0
    while changed
        changed = false
        # Add "named" object dependencies
        for obj in objs
            def = edges.byname[obj].assigned
            if !all(i->isrequired[i], def)
                changed = true
                for d in def
                    isrequired[d] = true
                    add_preds!(isrequired, d, edges)
                    if isexpr(src.code[d], :thunk) && startswith(String(obj), '#')
                        # For anonymous types, we also want their associated methods
                        add_succs!(isrequired, d, edges, edges.byname[obj].succs)
                    end
                end
            end
        end
        # Add "numbered" dependencies
        for idx = 1:length(isrequired)
            if isrequired[idx]
                preds = edges.preds[idx]
                if !all(i->isrequired[i], preds)
                    changed = true
                    isrequired[preds] .= true
                end
            end
        end
        # Add control-flow. For any basic block with an evaluated statement inside it,
        # check to see if the block has any successors, and if so mark that block's exit statement.
        # Likewise, any preceding blocks should have *their* exit statement marked.
        for (i, bb) in enumerate(bbs.blocks)
            r = rng(bb)
            if any(view(isrequired, r))
                # if !isempty(bb.succs)
                if i != length(bbs.blocks)
                    idxlast = r[end]
                    changed |= !isrequired[idxlast]
                    isrequired[idxlast] = true
                end
                for ibb in bb.preds
                    rpred = rng(bbs.blocks[ibb])
                    idxlast = rpred[end]
                    changed |= !isrequired[idxlast]
                    isrequired[idxlast] = true
                end
                for ibb in bb.succs
                    ibb == length(bbs.blocks) && continue
                    rpred = rng(bbs.blocks[ibb])
                    idxlast = rpred[end]
                    changed |= !isrequired[idxlast]
                    isrequired[idxlast] = true
                end
            end
        end
        # In preparation for the next round, add any new named objects
        # required by these dependencies
        for (obj, uses) in edges.byname
            obj ∈ objs && continue
            if any(i->isrequired[i], uses.succs)
                push!(objs, obj)
                changed = true
            end
        end
        iter += 1  # just for diagnostics
    end
    return isrequired
end

function caller_matches(f, mod, sym)
    is_global_ref(f, mod, sym) && return true
    if isdefined(mod, sym)
        is_quotenode(f, getfield(mod, sym)) && return true
    end
    return false
end

"""
    selective_eval!([recurse], frame::Frame, isrequired::AbstractVector{Bool}, istoplevel=false)

Execute the code in `frame` in the manner of `JuliaInterpreter.finish_and_return!`,
but skipping all statements that are marked `false` in `isrequired`.
See [`lines_required`](@ref). Upon entry, if needed the caller must ensure that `frame.pc` is
set to the correct statement, typically `findfirst(isrequired)`.
See [`selective_eval_fromstart!`](@ref) to have that performed automatically.

The default value for `recurse` is `JuliaInterpreter.finish_and_return!`.
`isrequired` pertains only to `frame` itself, not any of its callees.

This will return either a `BreakpointRef`, the value obtained from the last executed statement
(if stored to `frame.framedata.ssavlues`), or `nothing`.
Typically, assignment to a variable binding does not result in an ssa store by JuliaInterpreter.
"""
function selective_eval!(@nospecialize(recurse), frame::Frame, isrequired::AbstractVector{Bool}, istoplevel::Bool=false)
    pc = pcexec = pclast = frame.pc
    while pc !== nothing && !isa(pc, BreakpointRef)
        frame.pc = pc
        te = isrequired[pc]
        pclast = pcexec
        pc = te ? step_expr!(recurse, frame, istoplevel) :
                  next_or_nothing!(frame)
        pcexec = te ? pc : pcexec
    end
    isa(pc, BreakpointRef) && return pc
    pcexec = pcexec === nothing ? pclast : pcexec
    frame.pc = pcexec
    node = pc_expr(frame)
    isexpr(node, :return) && return @lookup(frame, (node::Expr).args[1])
    isassigned(frame.framedata.ssavalues, pcexec) && return frame.framedata.ssavalues[pcexec]
    return nothing
end
function selective_eval!(frame::Frame, isrequired::AbstractVector{Bool}, istoplevel::Bool=false)
    selective_eval!(finish_and_return!, frame, isrequired, istoplevel)
end

"""
    selective_eval_fromstart!([recurse], frame, isrequired, istoplevel=false)

Like [`selective_eval!`](@ref), except it sets `frame.pc` to the first `true` statement in `isrequired`.
"""
function selective_eval_fromstart!(@nospecialize(recurse), frame, isrequired, istoplevel::Bool=false)
    pc = findfirst(isrequired)
    pc === nothing && return nothing
    frame.pc = pc
    return selective_eval!(recurse, frame, isrequired, istoplevel)
end
function selective_eval_fromstart!(frame::Frame, isrequired::AbstractVector{Bool}, istoplevel::Bool=false)
    selective_eval_fromstart!(finish_and_return!, frame, isrequired, istoplevel)
end

"""
    print_with_code(io, src::CodeInfo, isrequired::AbstractVector{Bool})

Mark each line of code with its requirement status.

!!! compat Julia 1.6
    This function produces dummy output if suitable support is missing in your version of Julia.
"""
function print_with_code(io::IO, src::CodeInfo, isrequired::AbstractVector{Bool})
    nd = ndigits(length(isrequired))
    preprint(::IO) = nothing
    preprint(io::IO, idx::Int) = print(io, lpad(idx, nd), ' ', isrequired[idx] ? "t " : "f ")
    postprint(::IO) = nothing
    postprint(io::IO, idx::Int, bbchanged::Bool) = nothing

    print_with_code(preprint, postprint, io, src)
end

function print_with_code(io::IO, frame::Frame, obj)
    src = frame.framecode.src
    if isdefined(JuliaInterpreter, :reverse_lookup_globalref!)
        src = JuliaInterpreter.copy_codeinfo(src)
        JuliaInterpreter.reverse_lookup_globalref!(src.code)
    end
    print_with_code(io, src, obj)
end
