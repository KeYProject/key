#!/bin/sh
export PATH=$PATH:/home/hudson/key/bin/
git clean -x -d -f -q

# clean the settings to start with a defined configuration
rm -rf /var/lib/jenkins/.key/

