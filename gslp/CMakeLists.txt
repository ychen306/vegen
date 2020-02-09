add_library(GSLP MODULE GSLP.cpp)

set_target_properties(GSLP PROPERTIES
    COMPILE_FLAGS "-fno-rtti"
)

if(APPLE)
  set_target_properties(GSLP PROPERTIES
        LINK_FLAGS "-undefined dynamic_lookup")
endif(APPLE)
