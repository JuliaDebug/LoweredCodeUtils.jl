# Edges

Edges here are a graph-theoretic concept relating the connections between individual statements in the source code.
For example, consider

```julia
julia> ex = quote
           s = 0
           k = 5
           for i = 1:3
               global s, k
               s += rand(1:5)
               k += i
           end
       end
quote
    #= REPL[19]:2 =#
    s = 0
    #= REPL[19]:3 =#
    for i = 1:3
        #= REPL[19]:4 =#
        global s
        #= REPL[19]:5 =#
        s += rand(1:5)
    end
end

julia> eval(ex)

julia> s
10    # random

julia> k
11    # reproducible
```

We lower it,

```
julia> lwr = Meta.lower(Main, ex)
:($(Expr(:thunk, CodeInfo(
    @ REPL[19]:2 within `top-level scope'
1 ─       s = 0
│   @ REPL[19]:3 within `top-level scope'
│   %2  = 1:3
│         #s2 = Base.iterate(%2)
│   %4  = #s2 === nothing
│   %5  = Base.not_int(%4)
└──       goto #4 if not %5
2 ┄ %7  = #s2
│         i = Core.getfield(%7, 1)
│   %9  = Core.getfield(%7, 2)
│   @ REPL[19]:4 within `top-level scope'
│         global s
│   @ REPL[19]:5 within `top-level scope'
│   %11 = 1:5
│   %12 = rand(%11)
│   %13 = s + %12
│         s = %13
│         #s2 = Base.iterate(%2, %9)
│   %16 = #s2 === nothing
│   %17 = Base.not_int(%16)
└──       goto #4 if not %17
3 ─       goto #2
4 ┄       return
))))
```

and then extract the edges:

```julia
julia> edges = CodeEdges(lwr.args[1])
CodeEdges:
  s: assigned on [1, 14], depends on [13], and used by [10, 13]
  statement  1 depends on [13, 14] and is used by [10, 13, 14]
  statement  2 depends on ∅ and is used by [3, 15]
  statement  3 depends on [2, 9, 15] and is used by [4, 7, 15, 16]
  statement  4 depends on [3, 15] and is used by [5]
  statement  5 depends on [4] and is used by [6]
  statement  6 depends on [5] and is used by ∅
  statement  7 depends on [3, 15] and is used by [8, 9]
  statement  8 depends on [7] and is used by ∅
  statement  9 depends on [7] and is used by [3, 15]
  statement 10 depends on [1, 14] and is used by ∅
  statement 11 depends on ∅ and is used by [12]
  statement 12 depends on [11] and is used by [13]
  statement 13 depends on [1, 12, 14] and is used by [1, 14]
  statement 14 depends on [1, 13] and is used by [1, 10, 13]
  statement 15 depends on [2, 3, 9] and is used by [3, 4, 7, 16]
  statement 16 depends on [3, 15] and is used by [17]
  statement 17 depends on [16] and is used by [18]
  statement 18 depends on [17] and is used by ∅
  statement 19 depends on ∅ and is used by ∅
  statement 20 depends on ∅ and is used by ∅
```

This shows the dependencies of each line as well as the "named
variable" `s`.  It's worth looking specifically to see how the
slot-variable `#s2` gets handled, as you'll notice there is no mention
of this in the "variables" section at the bottom.  You can see that
`#s2` first gets assigned on line 3, which you'll notice depends on 2
(via the SSAValue printed as `%2`, but also on 9 and 15.  You can see
that line 15 is the 2-argument call to `iterate`, and that this line
depends on SSAValue `%9` (the state variable).  Consequently all the
line-dependencies of this slot variable have been aggregated into a
single list.

On suitable versions of Julia, an even more useful output can be obtained from the following:
```
julia> LoweredCodeUtils.print_with_code(stdout, lwr.args[1], edges)
Names:
s: assigned on [1, 14], depends on [13], and used by [10, 13]
Code:
1 ─       s = 0
             # preds: [13, 14], succs: [10, 13, 14]
│   %2  = 1:3
             # preds: ∅, succs: [3, 15]
│         _1 = Base.iterate(%2)
             # preds: [2, 9, 15], succs: [4, 7, 15, 16]
│   %4  = _1 === nothing
             # preds: [3, 15], succs: [5]
│   %5  = Base.not_int(%4)
             # preds: [4], succs: [6]
└──       goto #4 if not %5
             # preds: [5], succs: ∅
2 ┄ %7  = _1
             # preds: [3, 15], succs: [8, 9]
│         _2 = Core.getfield(%7, 1)
             # preds: [7], succs: ∅
│   %9  = Core.getfield(%7, 2)
             # preds: [7], succs: [3, 15]
│         global s
             # preds: [1, 14], succs: ∅
│   %11 = 1:5
             # preds: ∅, succs: [12]
│   %12 = rand(%11)
             # preds: [11], succs: [13]
│   %13 = s + %12
             # preds: [1, 12, 14], succs: [1, 14]
│         s = %13
             # preds: [1, 13], succs: [1, 10, 13]
│         _1 = Base.iterate(%2, %9)
             # preds: [2, 3, 9], succs: [3, 4, 7, 16]
│   %16 = _1 === nothing
             # preds: [3, 15], succs: [17]
│   %17 = Base.not_int(%16)
             # preds: [16], succs: [18]
└──       goto #4 if not %17
             # preds: [17], succs: ∅
3 ─       goto #2
             # preds: ∅, succs: ∅
4 ┄       return
             # preds: ∅, succs: ∅
```

Here the edges are printed right after each line.

!!! note
    Useful output from `print_with_code` requires at least version 1.6 of Julia.

Suppose we want to evaluate just the lines needed to compute `s`.
We can find out which lines these are with

```julia
julia> isrequired = lines_required(:s, lwr.args[1], edges)
24-element BitArray{1}:
 1
 0
 1
 1
 1
 1
 1
 1
 0
 1
 0
 0
 1
 1
 1
 1
 0
 0
 1
 1
 1
 1
 1
 0
```

and display them (given a suitable version of Julia) with

```
julia> LoweredCodeUtils.print_with_code(stdout, lwr.args[1], isrequired)
 1 t 1 ─       s = 0
 2 f │         k = 5
 3 t │   %3  = 1:3
 4 t │         _1 = Base.iterate(%3)
 5 t │   %5  = _1 === nothing
 6 t │   %6  = Base.not_int(%5)
 7 t └──       goto #4 if not %6
 8 t 2 ┄ %8  = _1
 9 f │         _2 = Core.getfield(%8, 1)
10 t │   %10 = Core.getfield(%8, 2)
11 f │         global k
12 f │         global s
13 t │   %13 = 1:5
14 t │   %14 = rand(%13)
15 t │   %15 = s + %14
16 t │         s = %15
17 f │   %17 = k + _2
18 f │         k = %17
19 t │         _1 = Base.iterate(%3, %10)
20 t │   %20 = _1 === nothing
21 t │   %21 = Base.not_int(%20)
22 t └──       goto #4 if not %21
23 t 3 ─       goto #2
24 f 4 ┄       return
```

We can test this with the following:

```julia
julia> using JuliaInterpreter

julia> frame = JuliaInterpreter.prepare_thunk(Main, lwr)
Frame for Main
   1 2  1 ─       s = 0
   2 3  │         k = 5
   3 4  │   %3  = 1:3
⋮

julia> k
11

julia> k = 0
0

julia> selective_eval_fromstart!(frame, isrequired, true)

julia> k
0

julia> s
12     # random

julia> selective_eval_fromstart!(frame, isrequired, true)

julia> k
0

julia> s
9      # random
```

You can see that `k` was not reset to its value of 11 when we ran this code selectively,
but that `s` was updated (to a random value) each time.
