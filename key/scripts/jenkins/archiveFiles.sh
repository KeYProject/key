cd #!/bin/sh -x
export KEY_VERSION="2.5.$BUILD_NUMBER"
export ANT_HOME=/opt/ant/
export ANT_OPTS="-Xmx2048m -Xms512m"
export PATH=$PATH:/home/hudson/key/bin/
export STATISTICS_DIR="$JENKINS_HOME/userContent/reports-$JOB_NAME"
unset DISPLAY

FILES=../key.nui/reports/*.htm*
PREFIX="${BUILD_NUMBER}_"

mkdir -p "$STATISTICS_DIR/$BUILD_NUMBER"
for file in $FILES
do
	echo "../key.nui/reports/$file"
	echo "$STATISTICS_DIR/$BUILD_NUMBER/$file"
	cp "../key.nui/reports/$file" "$STATISTICS_DIR/$BUILD_NUMBER/$file"
done

