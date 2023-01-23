#!/bin/sh -x
unset DISPLAY
export KEY_VERSION="2.9.$BUILD_NUMBER"
export PATH=$PATH:/home/hudson/key/bin/
export STATISTICS_DIR="$JENKINS_HOME/userContent/statistics-$JOB_NAME"

#
# Run unit tests
#
cd key
./gradlew --continue key.core.symbolic_execution:test key.core.proof_references:test
EXIT_UNIT_TESTS=$?

# Adapt to old scheme. copy tests xml to a folder where jenkins find them.
# Change if there is no ant build.
# Old regex: key/**/testresults/*.xml
XMLTESTFOLDER="xxx/testresults"
rm -rf $XMLTESTFOLDER
mkdir -p $XMLTESTFOLDER
find -iname 'TEST-*.xml' -exec cp {} $XMLTESTFOLDER \;

#
# create statistics if successful
#
mkdir -p "$STATISTICS_DIR"
# just for testing purposes  commented out
if [ "$EXIT_UNIT_TESTS" -eq "0" ]
then
  # MU: assumed changed current directory.
  # cp ../key.core.test/testresults/runallproofs/runStatistics.csv "$STATISTICS_DIR/$BUILD_NUMBER.csv"
  cp key.core.test/testresults/runallproofs/runStatistics.csv "$STATISTICS_DIR/$BUILD_NUMBER.csv"
  exit 0
else 
  exit 1
fi

