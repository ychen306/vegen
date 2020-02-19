add_library(GSLP MODULE GSLP.cpp InstSema.cpp)

set_target_properties(GSLP PROPERTIES
    COMPILE_FLAGS "-fno-rtti"
)

# THANKS AJAY!
set(INST_WRAPPERS "${CMAKE_BINARY_DIR}/InstWrappers.bc")
add_custom_command(OUTPUT ${INST_WRAPPERS}
  COMMAND clang -O3 -emit-llvm -march=skylake-avx512 ${CMAKE_CURRENT_SOURCE_DIR}/InstWrappers.c -c -Wno-argument-outside-range
    DEPENDS InstWrappers.c
	VERBATIM
)

add_custom_target(intrinsic_defs ALL DEPENDS ${INST_WRAPPERS})

if(APPLE)
  set_target_properties(GSLP PROPERTIES
        LINK_FLAGS "-undefined dynamic_lookup")
endif(APPLE)
