#!/bin/sh
sed '/version=/ c\
version="'$2'"

' $1 > tmp.plugin
mv tmp.plugin $1

