

llvm_map_components_to_libnames(llvm_libs support core bitreader bitwriter irreader analysis instrumentation)

add_executable(LiptonBin
                    util/BitMatrix.cpp
                    util/SCCQuotientGraph.cpp
                    llvm/ReachPass.cpp
                    Lipton.cpp)

# Link against LLVM libraries

if(APPLE)
#    target_link_libraries(LiptonBin "-Wl,-undefined,dynamic_lookup")
endif()

#target_link_libraries(LiptonBin "-Wl,-flat_namespace -Wl,-bundle -Wl,-undefined,error")
target_link_libraries(LiptonBin ${llvm_libs})
#target_link_libraries(LiptonBin     "-Wl,--start-group ${llvm_libs} -Wl,--end-group")
