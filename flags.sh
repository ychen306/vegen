VEGEN_BUILD_DIR=$1
export CLANG_FLAGS="-Xclang -load -Xclang ${VEGEN_BUILD_DIR}/gslp/libGSLP.so -O3 -fno-slp-vectorize -fno-vectorize -mllvm --wrappers-dir=${VEGEN_BUILD_DIR}"
