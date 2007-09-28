#!/bin/sh
sed 's/\" version=\"[^\"]*\"/\" version=\"'$2'\"/g;' $1 > tmp.plugin
mv tmp.plugin $1

