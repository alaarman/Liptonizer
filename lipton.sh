#!/bin/bash

C=$1

BC=${C/%c/bc}
BC=${BC/%cpp/bc}

set -e

clang -emit-llvm -c $1 -o $BC

llvm-dis $BC

OPT=${BC/%\.bc/-opt.bc}

opt -mem2reg \
    -internalize-public-api-list=main \
    -inline \
    -loops \
    -loop-simplify \
    -loop-rotate \
    -lcssa \
    -loop-unroll \
    -instnamer \
    $BC > $OPT

llvm-dis $OPT
    
L=${OPT/%\.bc/-lipton.bc}

./LiptonPass ${@:2} < $OPT > $L 

llvm-dis $L
