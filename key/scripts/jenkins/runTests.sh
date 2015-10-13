#!/bin/sh -x
export KEY_VERSION="2.5.$BUILD_NUMBER"
export ANT_HOME=/opt/ant/
export ANT_OPTS="-Xmx2048m -Xms512m"
export PATH=$PATH:/home/hudson/key/bin/
export STATISTICS_DIR="$JENKINS_HOME/userContent/statistics-$JOB_NAME"
unset DISPLAY

#
# Run unit tests
#
cd key/scripts
ant -logger org.apache.tools.ant.NoBannerLogger test-deploy-all
EXIT_UNIT_TESTS=$?

#
# create statistics if successful
#
mkdir -p "$STATISTICS_DIR"
# just for testing purposes  commented out
if [ "$EXIT_UNIT_TESTS" -eq "0" ]
then 
  cp ../key.core.test/testresults/runallproofs/runStatistics.csv "$STATISTICS_DIR/$BUILD_NUMBER.csv"
  exit 0
else 
  exit 1
fi

