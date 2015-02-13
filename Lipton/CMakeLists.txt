

llvm_map_components_to_libnames(llvm_libs support core irreader)

add_library(Lipton MODULE Lipton.cpp)

# Link against LLVM libraries


if(APPLE)
    target_link_libraries(Lipton "-Wl,-undefined,dynamic_lookup")
endif()

target_link_libraries(Lipton ${llvm_libs})
