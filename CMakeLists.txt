

cmake_minimum_required(VERSION 3.0.0)

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

message(STATUS "Using LLVM binaries from in: ${LLVM_TOOLS_BINARY_DIR}")

project(LLVMPass CXX)


SET (CMAKE_C_COMPILER             "clang")
SET (CMAKE_C_FLAGS                "-Wall -std=c99")
SET (CMAKE_C_FLAGS_DEBUG          "-g -O0")
SET (CMAKE_C_FLAGS_MINSIZEREL     "-Os -DNDEBUG")
SET (CMAKE_C_FLAGS_RELEASE        "-O4 -DNDEBUG")
SET (CMAKE_C_FLAGS_RELWITHDEBINFO "-O2 -g")

SET (CMAKE_CXX_COMPILER             "clang++")
SET (CMAKE_CXX_FLAGS                "-Wall -std=c++11")
SET (CMAKE_CXX_FLAGS_DEBUG          "-g -O0")
SET (CMAKE_CXX_FLAGS_MINSIZEREL     "-Os -DNDEBUG")
SET (CMAKE_CXX_FLAGS_RELEASE        "-O4 -DNDEBUG")
SET (CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O2 -g")

SET (CMAKE_AR      "${LLVM_TOOLS_BINARY_DIR}/llvm-ar")
SET (CMAKE_LINKER  "${LLVM_TOOLS_BINARY_DIR}/llvm-ld")
SET (CMAKE_NM      "${LLVM_TOOLS_BINARY_DIR}/llvm-nm")
SET (CMAKE_OBJDUMP "${LLVM_TOOLS_BINARY_DIR}/llvm-objdump")
SET (CMAKE_RANLIB  "${LLVM_TOOLS_BINARY_DIR}/llvm-ranlib")

#add_definitions("-std=c++11")


include_directories(${LLVM_INCLUDE_DIRS})
add_definitions( ${LLVM_DEFINITIONS} )



llvm_map_components_to_libnames(llvm_libs support core bitreader bitwriter
                                irreader mc transformutils analysis
                                instrumentation object ipo ipa
                                objcarcopts codegen tablegen)


add_executable(LiptonPass
                    util/BitMatrix.cpp
                    util/SCCQuotientGraph.cpp
                    llvm/ReachPass.cpp
                    llvm/LiptonPass.cpp
                    Lipton.cpp)


include_directories(LiptonPass . ~/andersen/include/ ${LLVM_INCLUDE_DIRS})


FIND_LIBRARY(ANDERS_LIBRARY Anders lib)
TARGET_LINK_LIBRARIES(LiptonPass ${ANDERS_LIBRARY})

# Link against LLVM libraries
target_link_libraries(LiptonPass ${llvm_libs})

