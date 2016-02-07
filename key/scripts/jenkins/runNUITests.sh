#!/bin/sh -x
export KEY_VERSION="2.5.$BUILD_NUMBER"
export ANT_HOME=/opt/ant/
export ANT_OPTS="-Xmx2048m -Xms512m"
export PATH=$PATH:/home/hudson/key/bin/
unset DISPLAY

#
# Run unit tests
#
cd key/key.nui
ant -logger org.apache.tools.ant.NoBannerLogger runTests