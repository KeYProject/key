#!/bin/sh
cd key/key.nui
export KEY_VERSION="2.5.$BUILD_NUMBER"
export ANT_HOME=/opt/ant/
export ANT_OPTS="-Xmx2048m -Xms512m"
export PATH=$PATH:/home/hudson/key/bin/
ant -logger org.apache.tools.ant.NoBannerLogger checkstyle
