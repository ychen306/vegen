# To build
You need `cmake` to build VeGen. VeGen depends on LLVM, and therefore you will
also need the *same* compiler that you used to compile LLVM to build VeGen for ABI compatibility.
```bash
export CXX=<the same c++ compiler you used to build llvm>
mkdir build
cd build
cmake $path_to_vegen
```

# To use
There are some flags that you would need to pass to `clang` in order to load vegen
as a plugin in to the optimization pipeline. To do this, do
```bash
source flags.sh $ABSOLUTE_PATH_TO_THE_BUILD_DIRECTORY
```
And then you can then for example do
```bash
clang $CLANG_FLAGS something.c -c -O3 -ffast-math
```

# Directory structure
`/gslp` (`gslp` used stand for Generalized SLP) 
  contains the vectorization heuristic and the code generation implementation.
`/sema` contains the semantics handling logic.
`/gslp/target-sema` and `gslp/target-wrappers` contains the code generated from `/sema`.
