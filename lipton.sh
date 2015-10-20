#!/bin/bash

C=$1

BC=${C/%c/bc}
BC=${BC/%cpp/bc}

set -e

CCODE=""

PIPE=$(mktemp -u)
mkfifo $PIPE
exec 3<>$PIPE
rm $PIPE

for a in `seq 2 $#`; do
	XX="${@:${a}}"
	if [ "$XX" == "-d" ]; then
		sed "s/<pthread.h>/<\/usr\/bin\/pthread.h>/g"  $1 >3
		break
	fi
done

if [ -z $CCODE ]; then
	cat $1 >3
fi

#echo <3

#echo "$CCODE" >3

clang -O0 -Iinclude -emit-llvm -Iic3-haskell/include/  -o $BC -c -x c - <3 #-O1 for TBAA

#clang -O1 -Iinclude -emit-llvm -Iic3-haskell/include/ -c $1 -o $BC #-O1 for TBAA

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
