VEGEN_BUILD_DIR=$1
export CLANG_FLAGS="-Xclang -load -Xclang ${VEGEN_BUILD_DIR}/gslp/libGSLP.so -fno-slp-vectorize -mllvm --wrappers-dir=${VEGEN_BUILD_DIR}"
