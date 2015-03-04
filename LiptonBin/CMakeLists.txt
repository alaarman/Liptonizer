
llvm_map_components_to_libnames(llvm_libs support core bitreader bitwriter
                                irreader mc transformutils analysis
                                instrumentation object ipo ipa
                                objcarcopts codegen tablegen)


add_executable(LiptonBin
                    util/BitMatrix.cpp
                    util/SCCQuotientGraph.cpp
                    llvm/ReachPass.cpp
                    llvm/LiptonPass.cpp
                    Lipton.cpp)

include_directories(.)

# Link against LLVM libraries
target_link_libraries(LiptonBin ${llvm_libs})
