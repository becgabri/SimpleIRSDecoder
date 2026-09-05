#!/bin/bash

for i in *.json; do
    echo "Running command with file $i"
    OUTP=$(sage ../decoder.sage 0 0 0 0 0 --file ./$i)
    echo "Finished command"
    echo "$OUTP"  
done
