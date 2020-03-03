add_executable(
  unittests
  TestSwizzle.cpp
  gtest-all.cpp
  main.cpp)

message(STATUS "!!!!!!!!!!!1 ${llvm_libs}")

target_link_libraries(
  unittests
  GSLP_AUX
  ${llvm_libs})

add_test(
  NAME
    unit
  COMMAND
    ${CMAKE_BINARY_DIR}/${CMAKE_INSTALL_BINDIR}/unittests
  )
