# LoweredCodeUtils

This package performs operations on Julia's [lowered AST](https://docs.julialang.org/en/latest/devdocs/ast/).
Current utilities include:
- `signature`: compute the signature of a specific method
- `methoddef!` extract all method signatures from a complete lowered block, resolving gensymmed names (https://github.com/JuliaLang/julia/issues/30908)

You can learn more about these with, e.g., `?methoddef!`
