PrecompileTools.@setup_workload let
    kwsrc = Meta.lower(@__MODULE__, :(f(x; color::Symbol=:green) = 2x)).args[1]
    ex = quote
        s = 0
        k = 5
        for i = 1:3
            global s, k
            s += rand(1:5)
            k += i
        end
    end
    src = Meta.lower(@__MODULE__, ex).args[1]
    PrecompileTools.@compile_workload let
        frame = Frame(@__MODULE__, kwsrc)
        rename_framemethods!(frame)
        edges = CodeEdges(@__MODULE__, src)
        isrequired = lines_required(GlobalRef(@__MODULE__, :s), src, edges)
        lines_required(GlobalRef(@__MODULE__, :s), src, edges; norequire=())
        lines_required(GlobalRef(@__MODULE__, :s), src, edges; norequire=exclude_named_typedefs(src))
        for isreq in (isrequired, convert(Vector{Bool}, isrequired))
            lines_required!(isreq, src, edges; norequire=())
            lines_required!(isreq, src, edges; norequire=exclude_named_typedefs(src))
        end
        frame = Frame(@__MODULE__, src)
        # selective_eval_fromstart!(frame, isrequired, true)
        precompile(selective_eval_fromstart!, (typeof(frame), typeof(isrequired), Bool))  # can't @eval during precompilation
        print_with_code(Base.inferencebarrier(devnull)::IO, src, edges)
        print_with_code(Base.inferencebarrier(devnull)::IO, src, isrequired)
    end
end
