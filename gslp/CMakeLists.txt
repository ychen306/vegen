include_directories(${CMAKE_CURRENT_BINARY_DIR})

# The main "lib packing"
set(LIB_PACKING_SRC
  target-sema/x86.cpp target-sema/arm.cpp

  Plan.cpp

  ControlEquivalence.cpp
  LoopFusion.cpp
  CodeMotionUtil.cpp

  VectorPack.cpp VectorPackContext.cpp VectorPackSet.cpp
  IntrinsicBuilder.cpp
  Heuristic.cpp
  Packer.cpp
  Solver.cpp
  IRVec.cpp
  MatchManager.cpp
  LocalDependenceAnalysis.cpp)


if(APPLE)
  add_library(Packing STATIC ${LIB_PACKING_SRC})
else()
  add_library(Packing SHARED ${LIB_PACKING_SRC})
endif(APPLE)

string(TOUPPER "${CMAKE_BUILD_TYPE}" BUILD_TYPE)

if(BUILD_TYPE STREQUAL "RELEASE")
  set_source_files_properties(
    ${LIB_PACKING_SRC} PROPERTIES COMPILE_FLAGS ${CMAKE_CXX_FLAGS_RELEASE})
  set_source_files_properties(
    target-sema/x86.cpp target-sema/arm.cpp
    PROPERTIES COMPILE_FLAGS "-O0")
endif()

add_library(GSLP MODULE GSLP.cpp)
add_executable(test-loop-fusion TestLoopFusion.cpp)

llvm_map_components_to_libnames(LLVM_LIBRARIES support core transformutils irreader analysis scalaropts)

target_link_libraries(GSLP Packing)

target_link_libraries(test-loop-fusion Packing ${LLVM_LIBRARIES})

set_target_properties(GSLP PROPERTIES COMPILE_FLAGS "-fno-rtti")

# THANKS AJAY!
set(X86_WRAPPERS "${CMAKE_BINARY_DIR}/x86.bc")
set(X86_FLAGS -mssse3 -msse -mavx512bw -msse3 -msse4.1 -msse4.2 -mfma -msse2 -mavx2 -mavx512vnni -mavx512vl -mavx512dq -mgfni -mavx512vbmi2 -mavx512vbmi -mavx512cd -mavx -mavx512f -mbmi2)
add_custom_command(OUTPUT ${X86_WRAPPERS}
  COMMAND clang -D__MM_MALLOC_H -target x86_64-unknown-none-gnu -O3 -emit-llvm ${X86_FLAGS} ${CMAKE_CURRENT_SOURCE_DIR}/target-wrappers/x86.c -c -Wno-argument-outside-range -o ${X86_WRAPPERS}
  DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/target-wrappers/x86.c
  VERBATIM
)

set(ARM_WRAPPERS "${CMAKE_BINARY_DIR}/arm.bc")
set(ARM_FLAGS -Xclang -target-feature -Xclang +neon -Xclang -target-feature -Xclang +dotprod) 
add_custom_command(OUTPUT ${ARM_WRAPPERS}
  COMMAND clang -D__MM_MALLOC_H -target aarch64-unknown-linux-gnu -O3 -emit-llvm ${ARM_FLAGS} ${CMAKE_CURRENT_SOURCE_DIR}/target-wrappers/arm.c -c -Wno-argument-outside-range -o ${ARM_WRAPPERS}
  DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/target-wrappers/arm.c
  VERBATIM
)

add_custom_target(intrinsic_defs ALL DEPENDS ${X86_WRAPPERS} ${ARM_WRAPPERS})

if(APPLE)
  set_target_properties(GSLP PROPERTIES
        LINK_FLAGS "-undefined dynamic_lookup")
endif(APPLE)
