# To build
Just build with CMake as usual, like
```bash
mkdir build
cd build
cmake $path_to_vegen
```

# Directory structure
`/gslp` (`gslp` used stand for Generalized SLP) 
  contains the vectorization heuristic and the code generation implementation.
`/sema` contains the semantics handling logic.
`/gslp/target-sema` and `gslp/target-wrappers` contains the code generated from `/sema`.
