cd #!/bin/sh -x
export KEY_VERSION="2.5.$BUILD_NUMBER"
export ANT_HOME=/opt/ant/
export ANT_OPTS="-Xmx2048m -Xms512m"
export PATH=$PATH:/home/hudson/key/bin/
export STATISTICS_DIR="$JENKINS_HOME/userContent/reports-$JOB_NAME"
unset DISPLAY

FILES=../key.nui/reports/*.htm*

mkdir -p "$STATISTICS_DIR/$BUILD_NUMBER"
for file in $FILES
do
	FILENAME=$(basename $file)
	cp "$file" "$STATISTICS_DIR/$BUILD_NUMBER/$FILENAME"
done

