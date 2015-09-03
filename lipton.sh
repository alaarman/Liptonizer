#!/bin/bash

C=$1

BC=${C/%c/bc}
BC=${BC/%cpp/bc}

set -e

clang -O0 -Iinclude -emit-llvm -c $1 -o $BC

llvm-dis $BC

OPT=${BC/%\.bc/-opt.bc}

opt -mem2reg -internalize-public-api-list=main -internalize -inline -loops \
    -loop-simplify -loop-rotate -lcssa -loop-unroll \
    $BC > $OPT

llvm-dis $OPT
    
F=${OPT/%\.bc/-lipton.bc}

./LiptonPass ${@:2} < $OPT > $F 

llvm-dis $F

FO=${F/%\.bc/-opt.bc}

opt -mem2reg -constprop -simplifycfg -globaldce -instnamer $F > $FO

llvm-dis $FO
