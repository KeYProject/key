#!/bin/sh
sed 's/feature url=\"[^\"]*\"/feature url=\"features\/KeY_Feature_'$2'.jar\"/g;' $1 > tmp.site
mv tmp.site $1
