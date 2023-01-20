#!/bin/sh
sed 's/Bundle-Version:[^$]*$/Bundle-Version: '$2'/g;' $1 > tmp.manifest
mv tmp.manifest $1

