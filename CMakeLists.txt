cmake_minimum_required(VERSION 3.4)
project(GSLP)

include(sanitizers.cmake)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

find_package(LLVM REQUIRED CONFIG)
message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(LLVM_BUILD_TOOLS ON)

add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})
add_definitions(-fno-rtti)
add_definitions(-std=c++14)

include_directories(gslp)
add_subdirectory(gslp)

configure_file(
  ${CMAKE_SOURCE_DIR}/test/lit.site.cfg.in
  ${CMAKE_BINARY_DIR}/test/lit.site.cfg
)

configure_file(
  ${CMAKE_SOURCE_DIR}/utils/vegen-clang.in
  ${CMAKE_BINARY_DIR}/vegen-clang
)

configure_file(
  ${CMAKE_SOURCE_DIR}/utils/vegen-clang.in
  ${CMAKE_BINARY_DIR}/vegen-clang++
)

configure_file(
  ${CMAKE_SOURCE_DIR}/utils/vegen-opt.in
  ${CMAKE_BINARY_DIR}/vegen-opt
)
