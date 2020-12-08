NUM_SIMULATIONS=1000
C=0.1
SOLVER=--use-bottom-up
VEGEN_BUILD_DIR=`readlink -f $1`
export CLANG_FLAGS="-O3 -Xclang -load -Xclang ${VEGEN_BUILD_DIR}/gslp/libGSLP.so -fno-slp-vectorize -mllvm --inst-wrappers=${VEGEN_BUILD_DIR}/InstWrappers.bc -march=native -ffast-math -mllvm --simulations=$NUM_SIMULATIONS -mllvm -c=$C -mllvm -w=25 -mllvm ${SOLVER} -mllvm --expand-after=0 -mllvm --max-search-dist=100 -mllvm --enum-cap=10000 -mllvm -max-num-lanes=64"
