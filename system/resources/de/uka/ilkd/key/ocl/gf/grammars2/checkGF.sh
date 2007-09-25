#!/bin/sh
GFA=gf_found

PLACE=`which gf`

if [ -z $PLACE ]
then
    echo 'then, no gf'
    if [ -f $GFA ]
    then
	rm $GFA
    fi
else
    echo 'else, gf'
    touch $GFA
fi