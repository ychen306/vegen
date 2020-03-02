add_executable(
  unittests
  TestSwizzle.cpp
  gtest-all.cpp
  main.cpp)

target_link_libraries(
  unittests
  GSLP_AUX)

add_test(
  NAME
    unit
  COMMAND
    ${CMAKE_BINARY_DIR}/${CMAKE_INSTALL_BINDIR}/unittests
  )
