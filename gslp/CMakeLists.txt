# The main "lib packing"
set(LIB_PACKING_SRC
  InstSema.cpp
  VectorPack.cpp VectorPackContext.cpp VectorPackSet.cpp
  IRModel.cpp Packer.cpp
  Solver.cpp
  IRVec.cpp
  LocalDependenceAnalysis.cpp)

if(APPLE)
  add_library(Packing STATIC ${LIB_PACKING_SRC})
else()
  add_library(Packing SHARED ${LIB_PACKING_SRC})
endif(APPLE)

# #xpose libPacking as a clang plugin
add_library(GSLP MODULE GSLP.cpp)

# Expose libPacking to the training code
add_executable(train train.cpp)

find_package(Torch REQUIRED)

SET_SOURCE_FILES_PROPERTIES(IRModel.cpp train.cpp GSLP.cpp PROPERTIES COMPILE_FLAGS "${CMAKE_CXX_FLAGS} ${TORCH_CXX_FLAGS}")


llvm_map_components_to_libnames(LLVM_LIBRARIES support core transformutils irreader analysis)

target_link_libraries(Packing ${TORCH_LIBRARIES})
target_link_libraries(GSLP Packing ${TORCH_LIBRARIES})
target_link_libraries(train Packing ${TORCH_LIBRARIES} ${LLVM_LIBRARIES})

SET_SOURCE_FILES_PROPERTIES(InstSema.cpp PROPERTIES COMPILE_FLAGS -O0)

set_target_properties(Packing PROPERTIES COMPILE_FLAGS "-frtti")

# THANKS AJAY!
set(INST_WRAPPERS "${CMAKE_BINARY_DIR}/InstWrappers.bc")
add_custom_command(OUTPUT ${INST_WRAPPERS}
  COMMAND clang -O3 -emit-llvm -march=skylake-avx512 ${CMAKE_CURRENT_SOURCE_DIR}/InstWrappers.c -c -Wno-argument-outside-range -o ${INST_WRAPPERS}
  DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/InstWrappers.c
  VERBATIM
)

add_custom_target(intrinsic_defs ALL DEPENDS ${INST_WRAPPERS})

if(APPLE)
  set_target_properties(GSLP PROPERTIES
        LINK_FLAGS "-undefined dynamic_lookup")
endif(APPLE)
