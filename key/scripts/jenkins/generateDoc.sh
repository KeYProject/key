#!/bin/sh -x
# API Doc generation to come
export KEY_VERSION="2.6.2"
export ANT_HOME=/opt/ant/
export ANT_OPTS="-Xmx2048m -Xms512m"
export PATH=$PATH:/home/hudson/key/bin/
cd key/scripts
ant generateDoc

