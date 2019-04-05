# LoweredCodeUtils

This package performs operations on Julia's [lowered AST](https://docs.julialang.org/en/latest/devdocs/ast/).
Current utilities include:
- `signature`: compute the signature of a specific method
- `methoddef!`: extract a method signature from lowered code, resolving gensymmed names (https://github.com/JuliaLang/julia/issues/30908)
- `bodymethod`: find the method that executes the body of a keyword-argument function

You can learn more about these with, e.g., `?methoddef!`
