cmake_minimum_required(VERSION 3.0.0)

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")


project(Lipton CXX)

add_definitions("-std=c++11")



include_directories(${LLVM_INCLUDE_DIRS})

add_definitions( ${LLVM_DEFINITIONS} )


#list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")
#include(AddLLVM)
#add_definitions( ${LLVM_DEFINITIONS} )
#link_directories( ${LLVM_LIBRARY_DIRS} )


add_library(Lipton MODULE Lipton.cpp)

llvm_map_components_to_libnames(llvm_libs support core)
# Link against LLVM libraries
target_link_libraries(Lipton ${llvm_libs} "-Wl,-undefined,dynamic_lookup")

# Find the libraries that correspond to the LLVM components
# that we wish to use
#llvm_map_components_to_libnames(REQ_LLVM_LIBRARIES support native)
#llvm_map_components_to_libnames(llvm_libs llvm support core irreader)


