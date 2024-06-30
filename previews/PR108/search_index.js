var documenterSearchIndex = {"docs":
[{"location":"api/#API","page":"API","title":"API","text":"","category":"section"},{"location":"api/#Signatures","page":"API","title":"Signatures","text":"","category":"section"},{"location":"api/","page":"API","title":"API","text":"signature\nmethoddef!\nrename_framemethods!\nbodymethod","category":"page"},{"location":"api/#LoweredCodeUtils.signature","page":"API","title":"LoweredCodeUtils.signature","text":"sig = signature(sigsv::SimpleVector)\n\nCompute a method signature from a suitable SimpleVector: sigsv[1] holds the signature and sigsv[2] the TypeVars.\n\nExample:\n\nFor f(x::AbstractArray{T}) where T, the corresponding sigsv is constructed as\n\nT = TypeVar(:T)\nsig1 = Core.svec(typeof(f), AbstractArray{T})\nsig2 = Core.svec(T)\nsigsv = Core.svec(sig1, sig2)\nsig = signature(sigsv)\n\n\n\n\n\nsigt, lastpc = signature(recurse, frame, pc)\nsigt, lastpc = signature(frame, pc)\n\nCompute the signature-type sigt of a method whose definition in frame starts at pc. Generally, pc should point to the Expr(:method, methname) statement, in which case lastpc is the final statement number in frame that is part of the signature (i.e, the line above the 3-argument :method expression). Alternatively, pc can point to the 3-argument :method expression, as long as all the relevant SSAValues have been assigned. In this case, lastpc == pc.\n\nIf no 3-argument :method expression is found, sigt will be nothing.\n\n\n\n\n\n","category":"function"},{"location":"api/#LoweredCodeUtils.methoddef!","page":"API","title":"LoweredCodeUtils.methoddef!","text":"ret = methoddef!(recurse, signatures, frame; define=true)\nret = methoddef!(signatures, frame; define=true)\n\nCompute the signature of a method definition. frame.pc should point to a :method expression. Upon exit, the new signature will be added to signatures.\n\nThere are several possible return values:\n\npc, pc3 = ret\n\nis the typical return. pc will point to the next statement to be executed, or be nothing if there are no further statements in frame. pc3 will point to the 3-argument :method expression.\n\nAlternatively,\n\npc = ret\n\noccurs for \"empty method\" expressions, e.g., :(function foo end). pc will be nothing.\n\nBy default the method will be defined (evaluated). You can prevent this by setting define=false. This is recommended if you are simply extracting signatures from code that has already been evaluated.\n\n\n\n\n\n","category":"function"},{"location":"api/#LoweredCodeUtils.rename_framemethods!","page":"API","title":"LoweredCodeUtils.rename_framemethods!","text":"methranges = rename_framemethods!(frame)\nmethranges = rename_framemethods!(recurse, frame)\n\nRename the gensymmed methods in frame to match those that are currently active. The issues are described in https://github.com/JuliaLang/julia/issues/30908. frame will be modified in-place as needed.\n\nReturns a vector of name=>start:stop pairs specifying the range of lines in frame at which method definitions occur. In some cases there may be more than one method with the same name in the start:stop range.\n\n\n\n\n\n","category":"function"},{"location":"api/#LoweredCodeUtils.bodymethod","page":"API","title":"LoweredCodeUtils.bodymethod","text":"mbody = bodymethod(m::Method)\n\nReturn the \"body method\" for a method m. mbody contains the code of the function body when m was defined.\n\n\n\n\n\n","category":"function"},{"location":"api/#Edges","page":"API","title":"Edges","text":"","category":"section"},{"location":"api/","page":"API","title":"API","text":"CodeEdges\nlines_required\nlines_required!\nselective_eval!\nselective_eval_fromstart!","category":"page"},{"location":"api/#LoweredCodeUtils.CodeEdges","page":"API","title":"LoweredCodeUtils.CodeEdges","text":"edges = CodeEdges(src::CodeInfo)\n\nAnalyze src and determine the chain of dependencies.\n\nedges.preds[i] lists the preceding statements that statement i depends on.\nedges.succs[i] lists the succeeding statements that depend on statement i.\nedges.byname[v] returns information about the predecessors, successors, and assignment statements for an object v::Union{GlobalRef, Symbol}.\n\n\n\n\n\n","category":"type"},{"location":"api/#LoweredCodeUtils.lines_required","page":"API","title":"LoweredCodeUtils.lines_required","text":"isrequired = lines_required(obj::Union{GlobalRef, Symbol}, src::CodeInfo, edges::CodeEdges)\nisrequired = lines_required(idx::Int,                     src::CodeInfo, edges::CodeEdges)\n\nDetermine which lines might need to be executed to evaluate obj or the statement indexed by idx. If isrequired[i] is false, the ith statement is not required. In some circumstances all statements marked true may be needed, in others control-flow will end up skipping a subset of such statements, perhaps while repeating others multiple times.\n\nSee also lines_required! and selective_eval!.\n\n\n\n\n\n","category":"function"},{"location":"api/#LoweredCodeUtils.lines_required!","page":"API","title":"LoweredCodeUtils.lines_required!","text":"lines_required!(isrequired::AbstractVector{Bool}, src::CodeInfo, edges::CodeEdges;\n                norequire = ())\n\nLike lines_required, but where isrequired[idx] has already been set to true for all statements that you know you need to evaluate. All other statements should be marked false at entry. On return, the complete set of required statements will be marked true.\n\nnorequire keyword argument specifies statements (represented as iterator of Ints) that should not be marked as a requirement. For example, use norequire = LoweredCodeUtils.exclude_named_typedefs(src, edges) if you're extracting method signatures and not evaluating new definitions.\n\n\n\n\n\n","category":"function"},{"location":"api/#LoweredCodeUtils.selective_eval!","page":"API","title":"LoweredCodeUtils.selective_eval!","text":"selective_eval!([recurse], frame::Frame, isrequired::AbstractVector{Bool}, istoplevel=false)\n\nExecute the code in frame in the manner of JuliaInterpreter.finish_and_return!, but skipping all statements that are marked false in isrequired. See lines_required. Upon entry, if needed the caller must ensure that frame.pc is set to the correct statement, typically findfirst(isrequired). See selective_eval_fromstart! to have that performed automatically.\n\nThe default value for recurse is JuliaInterpreter.finish_and_return!. isrequired pertains only to frame itself, not any of its callees.\n\nThis will return either a BreakpointRef, the value obtained from the last executed statement (if stored to frame.framedata.ssavlues), or nothing. Typically, assignment to a variable binding does not result in an ssa store by JuliaInterpreter.\n\n\n\n\n\n","category":"function"},{"location":"api/#LoweredCodeUtils.selective_eval_fromstart!","page":"API","title":"LoweredCodeUtils.selective_eval_fromstart!","text":"selective_eval_fromstart!([recurse], frame, isrequired, istoplevel=false)\n\nLike selective_eval!, except it sets frame.pc to the first true statement in isrequired.\n\n\n\n\n\n","category":"function"},{"location":"api/#Internal-utilities","page":"API","title":"Internal utilities","text":"","category":"section"},{"location":"api/","page":"API","title":"API","text":"LoweredCodeUtils.print_with_code\nLoweredCodeUtils.next_or_nothing\nLoweredCodeUtils.skip_until\nLoweredCodeUtils.MethodInfo\nLoweredCodeUtils.identify_framemethod_calls\nLoweredCodeUtils.iscallto\nLoweredCodeUtils.getcallee\nLoweredCodeUtils.find_name_caller_sig\nLoweredCodeUtils.replacename!\nLoweredCodeUtils.Variable","category":"page"},{"location":"api/#LoweredCodeUtils.print_with_code","page":"API","title":"LoweredCodeUtils.print_with_code","text":"print_with_code(io, src::CodeInfo, cl::CodeLinks)\n\nInterweave display of code and links.\n\ncompat: Julia 1.6\nThis function produces dummy output if suitable support is missing in your version of Julia.\n\n\n\n\n\nprint_with_code(io, src::CodeInfo, edges::CodeEdges)\n\nInterweave display of code and edges.\n\ncompat: Julia 1.6\nThis function produces dummy output if suitable support is missing in your version of Julia.\n\n\n\n\n\nprint_with_code(io, src::CodeInfo, isrequired::AbstractVector{Bool})\n\nMark each line of code with its requirement status.\n\ncompat: Julia 1.6\nThis function produces dummy output if suitable support is missing in your version of Julia.\n\n\n\n\n\n","category":"function"},{"location":"api/#LoweredCodeUtils.next_or_nothing","page":"API","title":"LoweredCodeUtils.next_or_nothing","text":"nextpc = next_or_nothing(frame, pc)\nnextpc = next_or_nothing!(frame)\n\nAdvance the program counter without executing the corresponding line. If frame is finished, nextpc will be nothing.\n\n\n\n\n\n","category":"function"},{"location":"api/#LoweredCodeUtils.skip_until","page":"API","title":"LoweredCodeUtils.skip_until","text":"nextpc = skip_until(predicate, frame, pc)\nnextpc = skip_until!(predicate, frame)\n\nAdvance the program counter until predicate(stmt) return true.\n\n\n\n\n\n","category":"function"},{"location":"api/#LoweredCodeUtils.MethodInfo","page":"API","title":"LoweredCodeUtils.MethodInfo","text":"MethodInfo(start, stop, refs)\n\nGiven a frame and its CodeInfo, start is the line of the first Expr(:method, name), whereas stop is the line of the last Expr(:method, name, sig, src) expression for name. refs is a vector of line numbers of other references. Some of these will be the location of the \"declaration\" of a method, the :thunk expression containing a CodeInfo that just returns a 1-argument :method expression. Others may be :global declarations.\n\nIn some cases there may be more than one method with the same name in the start:stop range.\n\n\n\n\n\n","category":"type"},{"location":"api/#LoweredCodeUtils.identify_framemethod_calls","page":"API","title":"LoweredCodeUtils.identify_framemethod_calls","text":"methodinfos, selfcalls = identify_framemethod_calls(frame)\n\nAnalyze the code in frame to locate method definitions and \"self-calls,\" i.e., calls to methods defined in frame that occur within frame.\n\nmethodinfos is a Dict of name=>info pairs, where info is a MethodInfo.\n\nselfcalls is a list of SelfCall(linetop, linebody, callee, caller) that holds the location of calls the methods defined in frame. linetop is the line in frame (top meaning \"top level\"), which will correspond to a 3-argument :method expression containing a CodeInfo body. linebody is the line within the CodeInfo body from which the call is made. callee is the Symbol of the called method.\n\n\n\n\n\n","category":"function"},{"location":"api/#LoweredCodeUtils.iscallto","page":"API","title":"LoweredCodeUtils.iscallto","text":"iscallto(stmt, name, src)\n\nReturns true is stmt is a call expression to name.\n\n\n\n\n\n","category":"function"},{"location":"api/#LoweredCodeUtils.getcallee","page":"API","title":"LoweredCodeUtils.getcallee","text":"getcallee(stmt)\n\nReturns the function (or Symbol) being called in a :call expression.\n\n\n\n\n\n","category":"function"},{"location":"api/#LoweredCodeUtils.find_name_caller_sig","page":"API","title":"LoweredCodeUtils.find_name_caller_sig","text":"pctop, isgen = find_name_caller_sig(recurse, frame, pc, name, parentname)\n\nScans forward from pc in frame until a method is found that calls name. pctop points to the beginning of that method's signature. isgen is true if name corresponds to sa GeneratedFunctionStub.\n\nAlternatively, this returns nothing if pc does not appear to point to either a keyword or generated method.\n\n\n\n\n\n","category":"function"},{"location":"api/#LoweredCodeUtils.replacename!","page":"API","title":"LoweredCodeUtils.replacename!","text":"replacename!(stmts, oldname=>newname)\n\nReplace a Symbol oldname with newname in stmts.\n\n\n\n\n\n","category":"function"},{"location":"api/#LoweredCodeUtils.Variable","page":"API","title":"LoweredCodeUtils.Variable","text":"Variable holds information about named variables. Unlike SSAValues, a single Variable can be assigned from multiple code locations.\n\nIf v is a Variable, then\n\nv.assigned is a list of statement numbers on which it is assigned\nv.preds is the set of statement numbers upon which this assignment depends\nv.succs is the set of statement numbers which make use of this variable\n\npreds and succs are short for \"predecessors\" and \"successors,\" respectively. These are meant in the sense of execution order, not statement number; depending on control-flow, a variable may have entries in preds that are larger than the smallest entry in assigned.\n\n\n\n\n\n","category":"type"},{"location":"#LoweredCodeUtils.jl","page":"Home","title":"LoweredCodeUtils.jl","text":"","category":"section"},{"location":"","page":"Home","title":"Home","text":"This package performs operations on Julia's lowered AST. An introduction to this representation can be found at JuliaInterpreter.","category":"page"},{"location":"","page":"Home","title":"Home","text":"Lowered AST (like other ASTs, type-inferred AST and SSA IR form) is generally more amenable to analysis than \"surface\" Julia expressions. However, sophisticated analyses can nevertheless require a fair bit of infrastructure. The purpose of this package is to standardize a few operations that are important in some applications.","category":"page"},{"location":"","page":"Home","title":"Home","text":"Currently there are two major domains of this package: the \"signatures\" domain and the \"edges\" domain.","category":"page"},{"location":"#Signatures","page":"Home","title":"Signatures","text":"","category":"section"},{"location":"","page":"Home","title":"Home","text":"A major role of this package is to support extraction of method signatures, in particular to provide strong support for relating keyword-method \"bodies\" to their parent methods. The central challenge this addresses is the lowering of keyword-argument functions and the fact that the \"gensymmed\" names are different each time you lower the code, and therefore you don't recover the actual (running) keyword-body method. The technical details are described in this Julia issue and on the next page. This package provides a workaround to rename gensymmed variables in newly-lowered code to match the name of the running keyword-body method, and provides a convenience function, bodymethod, to obtain that otherwise difficult-to-discover method.","category":"page"},{"location":"#Edges","page":"Home","title":"Edges","text":"","category":"section"},{"location":"","page":"Home","title":"Home","text":"Sometimes you want to run only a selected subset of code. For instance, Revise tracks methods by their signatures, and therefore needs to compute signatures from the lowered representation of code. Doing this robustly (including for @evaled methods, etc.) requires running module top-level code through the interpreter. For reasons of performance and safety, it is important to minimize the amount of code that gets executed when extracting the signature.","category":"page"},{"location":"","page":"Home","title":"Home","text":"This package provides a general framework for computing dependencies in code, through the CodeEdges constructor. It allows you to determine the lines on which any given statement depends, the lines which \"consume\" the result of the current line, and any \"named\" dependencies (Symbol and GlobalRef dependencies). In particular, this resolves the line-dependencies of all SlotNumber variables so that their own dependencies will be handled via the code-line dependencies.","category":"page"},{"location":"signatures/#Signatures-and-renaming","page":"Signatures and renaming","title":"Signatures and renaming","text":"","category":"section"},{"location":"signatures/","page":"Signatures and renaming","title":"Signatures and renaming","text":"We can demonstrate some of this package's functionality with the following simple example:","category":"page"},{"location":"signatures/","page":"Signatures and renaming","title":"Signatures and renaming","text":"julia> ex = :(f(x; color::Symbol=:green) = 2x)\n:(f(x; color::Symbol = :green) = begin\n          #= REPL[1]:1 =#\n          2x\n      end)\n\njulia> eval(ex)\nf (generic function with 1 method)\n\njulia> f(3)\n6","category":"page"},{"location":"signatures/","page":"Signatures and renaming","title":"Signatures and renaming","text":"Things get more interesting (and complicated) when we examine the lowered code:","category":"page"},{"location":"signatures/","page":"Signatures and renaming","title":"Signatures and renaming","text":"julia> lwr = Meta.lower(Main, ex)\n:($(Expr(:thunk, CodeInfo(\n    @ none within `top-level scope'\n1 ─       $(Expr(:thunk, CodeInfo(\n    @ none within `top-level scope'\n1 ─     return $(Expr(:method, :f))\n)))\n│         $(Expr(:thunk, CodeInfo(\n    @ none within `top-level scope'\n1 ─     return $(Expr(:method, Symbol(\"#f#2\")))\n)))\n│         $(Expr(:method, :f))\n│         $(Expr(:method, Symbol(\"#f#2\")))\n│   %5  = Core.typeof(var\"#f#2\")\n│   %6  = Core.Typeof(f)\n│   %7  = Core.svec(%5, Symbol, %6, Core.Any)\n│   %8  = Core.svec()\n│   %9  = Core.svec(%7, %8, $(QuoteNode(:(#= REPL[1]:1 =#))))\n│         $(Expr(:method, Symbol(\"#f#2\"), :(%9), CodeInfo(quote\n    $(Expr(:meta, :nkw, 1))\n    2 * x\n    return %2\nend)))\n│         $(Expr(:method, :f))\n│   %12 = Core.Typeof(f)\n│   %13 = Core.svec(%12, Core.Any)\n│   %14 = Core.svec()\n│   %15 = Core.svec(%13, %14, $(QuoteNode(:(#= REPL[1]:1 =#))))\n│         $(Expr(:method, :f, :(%15), CodeInfo(quote\n    var\"#f#2\"(:green, #self#, x)\n    return %1\nend)))\n│         $(Expr(:method, :f))\n│   %18 = Core.Typeof(f)\n│   %19 = Core.kwftype(%18)\n│   %20 = Core.Typeof(f)\n│   %21 = Core.svec(%19, Core.Any, %20, Core.Any)\n│   %22 = Core.svec()\n│   %23 = Core.svec(%21, %22, $(QuoteNode(:(#= REPL[1]:1 =#))))\n│         $(Expr(:method, :f, :(%23), CodeInfo(quote\n    Base.haskey(@_2, :color)\n    unless %1 goto %11\n    Base.getindex(@_2, :color)\n    %3 isa Symbol\n    unless %4 goto %7\n    goto %9\n    %new(Core.TypeError, Symbol(\"keyword argument\"), :color, Symbol, %3)\n    Core.throw(%7)\n    @_6 = %3\n    goto %12\n    @_6 = :green\n    color = @_6\n    Core.tuple(:color)\n    Core.apply_type(Core.NamedTuple, %13)\n    Base.structdiff(@_2, %14)\n    Base.pairs(%15)\n    Base.isempty(%16)\n    unless %17 goto %20\n    goto %21\n    Base.kwerr(@_2, @_3, x)\n    var\"#f#2\"(color, @_3, x)\n    return %21\nend)))\n│   %25 = f\n│   %26 = Core.ifelse(false, false, %25)\n└──       return %26\n))))","category":"page"},{"location":"signatures/","page":"Signatures and renaming","title":"Signatures and renaming","text":"This reveals the three methods actually got defined:","category":"page"},{"location":"signatures/","page":"Signatures and renaming","title":"Signatures and renaming","text":"one method of f with a single positional argument (this is the second 3-argument :method expression)\na keyword-handling method that checks the names of supplied keyword arguments and fills in defaults (this is the third 3-argument :method expression).  This method can be obtained from Core.kwfunc(f), which returns a function named f##kw.\na \"keyword-body\" method that actually does the work specifies by our function definition. This method gets called by the other two. (This is the first 3-argument :method expression.)","category":"page"},{"location":"signatures/","page":"Signatures and renaming","title":"Signatures and renaming","text":"From examining the lowered code we might guess that this function is called #f#2. What happens if we try to get it?","category":"page"},{"location":"signatures/","page":"Signatures and renaming","title":"Signatures and renaming","text":"julia> fbody = var\"#f#2\"\nERROR: UndefVarError: #f#2 not defined\nStacktrace:\n [1] top-level scope at REPL[6]:1","category":"page"},{"location":"signatures/","page":"Signatures and renaming","title":"Signatures and renaming","text":"Curiously, however, there is a closely-related function, and looking at its body code we see it is the one we wanted:","category":"page"},{"location":"signatures/","page":"Signatures and renaming","title":"Signatures and renaming","text":"julia> fbody = var\"#f#1\"\n#f#1 (generic function with 1 method)\n\njulia> mbody = first(methods(fbody))\n#f#1(color::Symbol, ::typeof(f), x) in Main at REPL[1]:1\n\njulia> Base.uncompressed_ast(mbody)\nCodeInfo(\n    @ REPL[1]:1 within `#f#1'\n1 ─      nothing\n│   %2 = 2 * x\n└──      return %2\n)","category":"page"},{"location":"signatures/","page":"Signatures and renaming","title":"Signatures and renaming","text":"It's named #f#1, rather than #f#2, because it was actually defined by that eval(ex) command at the top of this page. That eval caused it to be lowered once, and calling Meta.lower causes it to be lowered a second time, with different generated names.","category":"page"},{"location":"signatures/","page":"Signatures and renaming","title":"Signatures and renaming","text":"We can obtain the running version more directly (without having to guess) via the following:","category":"page"},{"location":"signatures/","page":"Signatures and renaming","title":"Signatures and renaming","text":"julia> m = first(methods(f))\nf(x; color) in Main at REPL[1]:1\n\njulia> using LoweredCodeUtils\n\njulia> bodymethod(m)\n#f#1(color::Symbol, ::typeof(f), x) in Main at REPL[1]:1","category":"page"},{"location":"signatures/","page":"Signatures and renaming","title":"Signatures and renaming","text":"We can also rename these methods, if we first turn it into a frame:","category":"page"},{"location":"signatures/","page":"Signatures and renaming","title":"Signatures and renaming","text":"julia> using JuliaInterpreter\n\njulia> frame = Frame(Main, lwr.args[1])\nFrame for Main\n   1 0  1 ─       $(Expr(:thunk, CodeInfo(\n   2 0  1 ─     return $(Expr(:method, :f))\n   3 0  )))\n⋮\n\njulia> rename_framemethods!(frame)\nDict{Symbol,LoweredCodeUtils.MethodInfo} with 3 entries:\n  :f             => MethodInfo(11, 24, [1])\n  Symbol(\"#f#2\") => MethodInfo(4, 10, [2])\n  Symbol(\"#f#1\") => MethodInfo(4, 10, [2])\n\njulia> frame.framecode.src\nCodeInfo(\n    @ none within `top-level scope'\n1 ─     $(Expr(:thunk, CodeInfo(\n    @ none within `top-level scope'\n1 ─     return $(Expr(:method, :f))\n)))\n│       $(Expr(:thunk, CodeInfo(\n    @ none within `top-level scope'\n1 ─     return $(Expr(:method, Symbol(\"#f#1\")))\n)))\n│       $(Expr(:method, :f))\n│       $(Expr(:method, Symbol(\"#f#1\")))\n│       ($(QuoteNode(typeof)))(var\"#f#1\")\n│       ($(QuoteNode(Core.Typeof)))(f)\n│       ($(QuoteNode(Core.svec)))(%J5, Symbol, %J6, $(QuoteNode(Any)))\n│       ($(QuoteNode(Core.svec)))()\n│       ($(QuoteNode(Core.svec)))(%J7, %J8, $(QuoteNode(:(#= REPL[1]:1 =#))))\n│       $(Expr(:method, Symbol(\"#f#1\"), %J9, CodeInfo(quote\n    $(Expr(:meta, :nkw, 1))\n    2 * x\n    return %2\nend)))\n│       $(Expr(:method, :f))\n│       ($(QuoteNode(Core.Typeof)))(f)\n│       ($(QuoteNode(Core.svec)))(%J12, $(QuoteNode(Any)))\n│       ($(QuoteNode(Core.svec)))()\n│       ($(QuoteNode(Core.svec)))(%J13, %J14, $(QuoteNode(:(#= REPL[1]:1 =#))))\n│       $(Expr(:method, :f, %J15, CodeInfo(quote\n    var\"#f#1\"(:green, #self#, x)\n    return %1\nend)))\n│       $(Expr(:method, :f))\n│       ($(QuoteNode(Core.Typeof)))(f)\n│       ($(QuoteNode(Core.kwftype)))(%J18)\n│       ($(QuoteNode(Core.Typeof)))(f)\n│       ($(QuoteNode(Core.svec)))(%J19, $(QuoteNode(Any)), %J20, $(QuoteNode(Any)))\n│       ($(QuoteNode(Core.svec)))()\n│       ($(QuoteNode(Core.svec)))(%J21, %J22, $(QuoteNode(:(#= REPL[1]:1 =#))))\n│       $(Expr(:method, :f, %J23, CodeInfo(quote\n    Base.haskey(@_2, :color)\n    unless %1 goto %11\n    Base.getindex(@_2, :color)\n    %3 isa Symbol\n    unless %4 goto %7\n    goto %9\n    %new(Core.TypeError, Symbol(\"keyword argument\"), :color, Symbol, %3)\n    Core.throw(%7)\n    @_6 = %3\n    goto %12\n    @_6 = :green\n    color = @_6\n    Core.tuple(:color)\n    Core.apply_type(Core.NamedTuple, %13)\n    Base.structdiff(@_2, %14)\n    Base.pairs(%15)\n    Base.isempty(%16)\n    unless %17 goto %20\n    goto %21\n    Base.kwerr(@_2, @_3, x)\n    var\"#f#1\"(color, @_3, x)\n    return %21\nend)))\n│       f\n│       ($(QuoteNode(ifelse)))(false, false, %J25)\n└──     return %J26\n)","category":"page"},{"location":"signatures/","page":"Signatures and renaming","title":"Signatures and renaming","text":"While there are a few differences in representation stemming from converting it to a frame, you can see that the #f#2s have been changed to #f#1s to match the currently-running names.","category":"page"},{"location":"edges/#Edges","page":"Edges","title":"Edges","text":"","category":"section"},{"location":"edges/","page":"Edges","title":"Edges","text":"Edges here are a graph-theoretic concept relating the connections between individual statements in the source code. For example, consider","category":"page"},{"location":"edges/","page":"Edges","title":"Edges","text":"julia> ex = quote\n           s = 0\n           k = 5\n           for i = 1:3\n               global s, k\n               s += rand(1:5)\n               k += i\n           end\n       end\nquote\n    #= REPL[2]:2 =#\n    s = 0\n    #= REPL[2]:3 =#\n    k = 5\n    #= REPL[2]:4 =#\n    for i = 1:3\n        #= REPL[2]:5 =#\n        global s, k\n        #= REPL[2]:6 =#\n        s += rand(1:5)\n        #= REPL[2]:7 =#\n        k += i\n    end\nend\n\njulia> eval(ex)\n\njulia> s\n10    # random\n\njulia> k\n11    # reproducible","category":"page"},{"location":"edges/","page":"Edges","title":"Edges","text":"We lower it,","category":"page"},{"location":"edges/","page":"Edges","title":"Edges","text":"julia> lwr = Meta.lower(Main, ex)\n:($(Expr(:thunk, CodeInfo(\n    @ REPL[2]:2 within `top-level scope'\n1 ─       s = 0\n│   @ REPL[2]:3 within `top-level scope'\n│         k = 5\n│   @ REPL[2]:4 within `top-level scope'\n│   %3  = 1:3\n│         #s1 = Base.iterate(%3)\n│   %5  = #s1 === nothing\n│   %6  = Base.not_int(%5)\n└──       goto #4 if not %6\n2 ┄ %8  = #s1\n│         i = Core.getfield(%8, 1)\n│   %10 = Core.getfield(%8, 2)\n│   @ REPL[2]:5 within `top-level scope'\n│         global k\n│         global s\n│   @ REPL[2]:6 within `top-level scope'\n│   %13 = 1:5\n│   %14 = rand(%13)\n│   %15 = s + %14\n│         s = %15\n│   @ REPL[2]:7 within `top-level scope'\n│   %17 = k + i\n│         k = %17\n│         #s1 = Base.iterate(%3, %10)\n│   %20 = #s1 === nothing\n│   %21 = Base.not_int(%20)\n└──       goto #4 if not %21\n3 ─       goto #2\n4 ┄       return\n))))","category":"page"},{"location":"edges/","page":"Edges","title":"Edges","text":"and then extract the edges:","category":"page"},{"location":"edges/","page":"Edges","title":"Edges","text":"julia> edges = CodeEdges(lwr.args[1])\nCodeEdges:\n  s: assigned on [1, 16], depends on [15], and used by [12, 15]\n  k: assigned on [2, 18], depends on [17], and used by [11, 17]\n  statement  1 depends on [15, 16] and is used by [12, 15, 16]\n  statement  2 depends on [17, 18] and is used by [11, 17, 18]\n  statement  3 depends on ∅ and is used by [4, 19]\n  statement  4 depends on [3, 10, 19] and is used by [5, 8, 19, 20]\n  statement  5 depends on [4, 19] and is used by [6]\n  statement  6 depends on [5] and is used by [7]\n  statement  7 depends on [6] and is used by ∅\n  statement  8 depends on [4, 19] and is used by [9, 10]\n  statement  9 depends on [8] and is used by [17]\n  statement 10 depends on [8] and is used by [4, 19]\n  statement 11 depends on [2, 18] and is used by ∅\n  statement 12 depends on [1, 16] and is used by ∅\n  statement 13 depends on ∅ and is used by [14]\n  statement 14 depends on [13] and is used by [15]\n  statement 15 depends on [1, 14, 16] and is used by [1, 16]\n  statement 16 depends on [1, 15] and is used by [1, 12, 15]\n  statement 17 depends on [2, 9, 18] and is used by [2, 18]\n  statement 18 depends on [2, 17] and is used by [2, 11, 17]\n  statement 19 depends on [3, 4, 10] and is used by [4, 5, 8, 20]\n  statement 20 depends on [4, 19] and is used by [21]\n  statement 21 depends on [20] and is used by [22]\n  statement 22 depends on [21] and is used by ∅\n  statement 23 depends on ∅ and is used by ∅\n  statement 24 depends on ∅ and is used by ∅","category":"page"},{"location":"edges/","page":"Edges","title":"Edges","text":"This shows the dependencies of each line as well as the \"named variables\" s and k.  It's worth looking specifically to see how the slot-variable #s1 gets handled, as you'll notice there is no mention of this in the \"variables\" section at the top.  You can see that #s1 first gets assigned on line 4 (the iterate statement), which you'll notice depends on 3 (via the SSAValue printed as %3). But that line 4 also is shown as depending on 10 and 19. You can see that line 19 is the 2-argument call to iterate, and that this line depends on SSAValue %10 (the state variable). Consequently all the line-dependencies of this slot variable have been aggregated into a single list by determining the \"global\" influences on that slot variable.","category":"page"},{"location":"edges/","page":"Edges","title":"Edges","text":"An even more useful output can be obtained from the following:","category":"page"},{"location":"edges/","page":"Edges","title":"Edges","text":"julia> LoweredCodeUtils.print_with_code(stdout, lwr.args[1], edges)\nNames:\ns: assigned on [1, 16], depends on [15], and used by [12, 15]\nk: assigned on [2, 18], depends on [17], and used by [11, 17]\nCode:\n1 ─       s = 0\n│             # preds: [15, 16], succs: [12, 15, 16]\n│         k = 5\n│             # preds: [17, 18], succs: [11, 17, 18]\n│   %3  = 1:3\n│             # preds: ∅, succs: [4, 19]\n│         _1 = Base.iterate(%3)\n│             # preds: [3, 10, 19], succs: [5, 8, 19, 20]\n│   %5  = _1 === nothing\n│             # preds: [4, 19], succs: [6]\n│   %6  = Base.not_int(%5)\n│             # preds: [5], succs: [7]\n└──       goto #4 if not %6\n              # preds: [6], succs: ∅\n2 ┄ %8  = _1\n│             # preds: [4, 19], succs: [9, 10]\n│         _2 = Core.getfield(%8, 1)\n│             # preds: [8], succs: [17]\n│   %10 = Core.getfield(%8, 2)\n│             # preds: [8], succs: [4, 19]\n│         global k\n│             # preds: [2, 18], succs: ∅\n│         global s\n│             # preds: [1, 16], succs: ∅\n│   %13 = 1:5\n│             # preds: ∅, succs: [14]\n│   %14 = rand(%13)\n│             # preds: [13], succs: [15]\n│   %15 = s + %14\n│             # preds: [1, 14, 16], succs: [1, 16]\n│         s = %15\n│             # preds: [1, 15], succs: [1, 12, 15]\n│   %17 = k + _2\n│             # preds: [2, 9, 18], succs: [2, 18]\n│         k = %17\n│             # preds: [2, 17], succs: [2, 11, 17]\n│         _1 = Base.iterate(%3, %10)\n│             # preds: [3, 4, 10], succs: [4, 5, 8, 20]\n│   %20 = _1 === nothing\n│             # preds: [4, 19], succs: [21]\n│   %21 = Base.not_int(%20)\n│             # preds: [20], succs: [22]\n└──       goto #4 if not %21\n              # preds: [21], succs: ∅\n3 ─       goto #2\n              # preds: ∅, succs: ∅\n4 ┄       return\n              # preds: ∅, succs: ∅","category":"page"},{"location":"edges/","page":"Edges","title":"Edges","text":"Here the edges are printed right after each line.","category":"page"},{"location":"edges/","page":"Edges","title":"Edges","text":"note: Note\n\"Nice\" output from print_with_code requires at least version 1.6.0-DEV.95 of Julia.","category":"page"},{"location":"edges/","page":"Edges","title":"Edges","text":"Suppose we want to evaluate just the lines needed to compute s. We can find out which lines these are with","category":"page"},{"location":"edges/","page":"Edges","title":"Edges","text":"julia> isrequired = lines_required(:s, lwr.args[1], edges)\n24-element BitArray{1}:\n 1\n 0\n 1\n 1\n 1\n 1\n 1\n 1\n 0\n 1\n 0\n 0\n 1\n 1\n 1\n 1\n 0\n 0\n 1\n 1\n 1\n 1\n 1\n 0","category":"page"},{"location":"edges/","page":"Edges","title":"Edges","text":"and display them with","category":"page"},{"location":"edges/","page":"Edges","title":"Edges","text":"julia> LoweredCodeUtils.print_with_code(stdout, lwr.args[1], isrequired)\n 1 t 1 ─       s = 0\n 2 f │         k = 5\n 3 t │   %3  = 1:3\n 4 t │         _1 = Base.iterate(%3)\n 5 t │   %5  = _1 === nothing\n 6 t │   %6  = Base.not_int(%5)\n 7 t └──       goto #4 if not %6\n 8 t 2 ┄ %8  = _1\n 9 f │         _2 = Core.getfield(%8, 1)\n10 t │   %10 = Core.getfield(%8, 2)\n11 f │         global k\n12 f │         global s\n13 t │   %13 = 1:5\n14 t │   %14 = rand(%13)\n15 t │   %15 = s + %14\n16 t │         s = %15\n17 f │   %17 = k + _2\n18 f │         k = %17\n19 t │         _1 = Base.iterate(%3, %10)\n20 t │   %20 = _1 === nothing\n21 t │   %21 = Base.not_int(%20)\n22 t └──       goto #4 if not %21\n23 t 3 ─       goto #2\n24 f 4 ┄       return","category":"page"},{"location":"edges/","page":"Edges","title":"Edges","text":"We can test this with the following:","category":"page"},{"location":"edges/","page":"Edges","title":"Edges","text":"julia> using JuliaInterpreter\n\njulia> frame = Frame(Main, lwr.args[1])\nFrame for Main\n   1 2  1 ─       s = 0\n   2 3  │         k = 5\n   3 4  │   %3  = 1:3\n⋮\n\njulia> k\n11\n\njulia> k = 0\n0\n\njulia> selective_eval_fromstart!(frame, isrequired, true)\n\njulia> k\n0\n\njulia> s\n12     # random\n\njulia> selective_eval_fromstart!(frame, isrequired, true)\n\njulia> k\n0\n\njulia> s\n9      # random","category":"page"},{"location":"edges/","page":"Edges","title":"Edges","text":"You can see that k was not reset to its value of 11 when we ran this code selectively, but that s was updated (to a random value) each time.","category":"page"}]
}
