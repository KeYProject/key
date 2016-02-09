#!/bin/sh -x
export KEY_VERSION="2.5.$BUILD_NUMBER"
export ANT_HOME=/opt/ant/
export ANT_OPTS="-Xmx2048m -Xms512m"
export PATH=$PATH:/home/hudson/key/bin/
export STATISTICS_DIR="$JENKINS_HOME/userContent/reports-$JOB_NAME"
unset DISPLAY

FILES=*.htm*
PREFIX="$BUILD_NUMBER" + "_"

cd ../key.nui/reports/

for file in $FILES
do
	cp $file "$STATISTICS_DIR/$BUILD_NUMBER/$PREFIX${f%%.*}.${f##*.}"
done

