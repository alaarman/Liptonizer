
#/opt/local/libexec/llvm-3.5/bin/clang++ -D__STDC_CONSTANT_MACROS -D__STDC_LIMIT_MACROS -Wall -std=c++11 -I/opt/local/libexec/llvm-3.5/include -o CMakeFiles/LiptonBin.dir/Lipton.cpp.o -c /Users/laarman/Workspace/LLVMpass/LiptonBin/Lipton.cpp

clang++ `llvm-config --cxxflags` -O0 Lipton.cpp  -o LiptonBin  `llvm-config --ldflags` `llvm-config --system-libs` `llvm-config --libs`
