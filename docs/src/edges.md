# Edges

Edges here are a graph-theoretic concept relating the connections between individual statements in the source code.
For example, consider

```julia
julia> ex = quote
           s = 0
           for i = 1:3
               global s
               s += rand(1:5)
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
10
```

We lower it,

```julia
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
julia> CodeEdges(lwr.args[1])
CodeEdges:
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
  s assigned on [1, 14], depends on [13], and used by [10, 13]
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
