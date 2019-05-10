#!/bin/sh -x
unset DISPLAY
export KEY_VERSION="2.7.$BUILD_NUMBER"
export JAVA_OPTS="-Xmx64m -XX:MaxPermSize=64m -Dfile.encoding=UTF-8"
export PATH=$PATH:/home/hudson/key/bin/
export STATISTICS_DIR="$JENKINS_HOME/userContent/statistics-$JOB_NAME"
export GRADLE_OPTS="-Dorg.gradle.daemon=false org.gradle.jvmargs=-Xmx2g -XX:MaxMetaspaceSize=512m -Dfile.encoding=UTF-8"
#
# Run unit tests
#
cd key
./gradlew test testProofRules testRunAllProofs --parallel
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

