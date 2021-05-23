include_directories(${CMAKE_CURRENT_BINARY_DIR})

# The main "lib packing"
set(LIB_PACKING_SRC
  target-sema/x86.cpp target-sema/arm.cpp

  VectorPack.cpp VectorPackContext.cpp VectorPackSet.cpp
  IntrinsicBuilder.cpp
  Heuristic.cpp
  Packer.cpp
  Solver.cpp
  IRVec.cpp
  LaneBinding.cpp
  Canonicalizer.cpp
  EnumerateSeeds.cpp
  MatchManager.cpp
  LocalDependenceAnalysis.cpp)

if(APPLE)
  add_library(Packing STATIC ${LIB_PACKING_SRC})
else()
  add_library(Packing SHARED ${LIB_PACKING_SRC})
endif(APPLE)

add_library(GSLP MODULE GSLP.cpp)

llvm_map_components_to_libnames(LLVM_LIBRARIES support core transformutils irreader analysis codegen x86desc x86info x86codegen)

#target_link_libraries(Packing ${LLVM_LIBRARIES})
target_link_libraries(GSLP Packing)

SET_SOURCE_FILES_PROPERTIES(
  target-sema/x86.cpp target-sema/arm.cpp 
  PROPERTIES COMPILE_FLAGS -O0)

set_target_properties(GSLP PROPERTIES COMPILE_FLAGS "-fno-rtti")

# THANKS AJAY!
set(INST_WRAPPERS "${CMAKE_BINARY_DIR}/x86.bc")
set(ALL_FLAGS -mssse3 -msse -mavx512bw -msse3 -msse4.1 -msse4.2 -mfma -msse2 -mavx2 -mavx512vnni -mavx512vl -mavx512dq -mgfni -mavx512vbmi2 -mavx512vbmi -mavx512cd -mavx -mavx512f -mbmi2)
add_custom_command(OUTPUT ${INST_WRAPPERS}
  COMMAND clang -O3 -emit-llvm ${ALL_FLAGS} ${CMAKE_CURRENT_SOURCE_DIR}/target-wrappers/x86.c -c -Wno-argument-outside-range -o ${INST_WRAPPERS}
  DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/target-wrappers/x86.c
  VERBATIM
)

add_custom_target(intrinsic_defs ALL DEPENDS ${INST_WRAPPERS})

if(APPLE)
  set_target_properties(GSLP PROPERTIES
        LINK_FLAGS "-undefined dynamic_lookup")
endif(APPLE)
