NUM_SIMULATIONS=1000
C=0.1
export CLANG_FLAGS="-O3 -Xclang -load -Xclang ${GSLP_BUILD_DIR}/gslp/libGSLP.so -fno-slp-vectorize -mllvm --inst-wrappers=${GSLP_BUILD_DIR}/InstWrappers.bc -march=native -ffast-math -mllvm --simulations=$NUM_SIMULATIONS -mllvm -c=$C -mllvm -w=25 -mllvm --use-bottom-up -mllvm --expand-after=0 -mllvm --max-search-dist=100 -mllvm --enum-cap=10000 -mllvm -max-num-lanes=32"
