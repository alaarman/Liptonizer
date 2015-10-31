#!/bin/bash

C=$1

BASE=${C/%.c/}
BC=${C/%c/bc}
BC=${BC/%cpp/bc}

set -e

CCODE=""

PIPE=$(mktemp -u)
mkfifo $PIPE
exec 3<>$PIPE
rm $PIPE

DEBUG=""
for a in `seq 2 $#`; do
	XX="${!a}"
	if [ "$XX" == "-d" ]; then
		sed "s/<pthread.h>/<\/usr\/include\/pthread.h>/g" $1 | \
			sed "s/<assert.h>/<\/usr\/include\/assert.h>/g" >3
		DEBUG="-g"
		echo "DEBUG MODE!!!!!!!!!!!!!!!!!!!!!"
		break
	fi
done

if [ -z "$DEBUG" ]; then
	echo "Normal mode"
	cat $1 >3
fi


#echo "$CCODE" >3

clang -O0 $DEBUG -Iinclude -fno-rtti -emit-llvm -Iic3-haskell/include/  -o $BC -c -x c - <3 #-O1 for TBAA

#clang -O1 -Iinclude -emit-llvm -Iic3-haskell/include/ -c $1 -o $BC #-O1 for TBAA

llvm-dis $BC

OPT=${BC/%\.bc/-opt.bc}

opt -mem2reg -internalize-public-api-list=main -internalize -inline -loops \
    -loop-simplify -loop-rotate -lcssa -loop-unroll \
    $BC > $OPT


llvm-dis $OPT

echo $OPT
    
F=${OPT/%\.bc/-lipton.bc}

./LiptonPass ${@:2} < $OPT > $F 

llvm-dis $F

FO=${F/%\.bc/-opt.bc}

opt -mem2reg -constprop -simplifycfg -globaldce -instnamer $F > $FO

llvm-dis $FO


if [ ! -z "$DEBUG" ]; then
    clang -O0 -g lib.c -shared -olib.so
    clang -O0 -g $BASE-opt-lipton.bc lib.so
    ./a.out
fi
