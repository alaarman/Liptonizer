#!/bin/bash

T=${1/.bc/-opt.bc}

opt -mem2reg \
    -internalize-public-api-list=main \
    -inline \
    -loops \
    -loop-simplify \
    -loop-rotate \
    -lcssa \
    -loop-unroll \
    -instnamer \
    $1 > $T

./LiptonBin $2 $T
