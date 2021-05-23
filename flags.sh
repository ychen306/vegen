VEGEN_BUILD_DIR=$1
export CLANG_FLAGS="-O3 -Xclang -load -Xclang ${VEGEN_BUILD_DIR}/gslp/libGSLP.so -fno-slp-vectorize -mllvm --wrappers-dir=${VEGEN_BUILD_DIR} -march=haswell -mavx2 -mavx512vnni -mavx512vl -mavx512f -ffast-math"
