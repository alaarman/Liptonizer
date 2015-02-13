cmake_minimum_required(VERSION 3.0.0)

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")


project(LLVMPass CXX)
add_definitions("-std=c++11")


include_directories(${LLVM_INCLUDE_DIRS})
add_definitions( ${LLVM_DEFINITIONS} )
llvm_map_components_to_libnames(llvm_libs support core)


add_subdirectory(Lipton)

