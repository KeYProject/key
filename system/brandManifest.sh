#!/bin/sh
sed '/Bundle-Version:/ c\
Bundle-Version: '$2'

' $1 > tmp.mf
#mv tmp.mf $1

