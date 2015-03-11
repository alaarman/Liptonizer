#!/bin/sh

MAX=$1
if [ -z "$MAX" ]; then
    MAX=1000
fi

for a in `seq 1 $MAX`; do
    ./ndfs;
    A=$?;
    if [ $A == 134 ]; then
        break;
    fi;
done

