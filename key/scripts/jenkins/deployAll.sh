#!/bin/sh
cd key/scripts
export ANT_HOME=/opt/ant/
export ANT_OPTS="-Xmx2048m -Xms512m"
export PATH=$PATH:/home/hudson/key/bin/
export KEY_VERSION="2.6.0"
ant -logger org.apache.tools.ant.NoBannerLogger deployAll

