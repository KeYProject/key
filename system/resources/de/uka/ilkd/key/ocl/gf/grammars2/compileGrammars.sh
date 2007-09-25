#!/bin/sh

# compileGrammars.sh takes two arguments:
# 1) the path to the GF grammars (compiled grammars will be saved there)
# 2) fallback path to key-ext-jars.  
#    Will be used when looking for the gf binary, if:
#        gf is not found in $PATH, and
#        $KEY_LIB is not defined
#    This should emulate the behaviour of the startkey script. 


LISTFILE=grammars2list.txt
GFOPTIONS=gfOptions.txt
# GFCOMMAND=gf

# look for the gf binary in the following order: $PATH, $KEY_LIB, $2
GFCOMMAND=`env "PATH=${PATH}:${KEY_LIB}:$2" which gf` 

cd $1
# ./checkGF.sh 2> /dev/null

if [ -x "$GFCOMMAND" ]
then
    echo "[GF grammars are being compiled]"
    echo $PWD
    $GFCOMMAND -batch < $GFOPTIONS > /dev/null
    echo "writing grammars2list.txt"
    find -name \*.gf\? > $LISTFILE
else
    echo "[gf not found; skipping compiling the grammars]"
fi
