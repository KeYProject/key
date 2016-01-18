#!/bin/sh
cd key/key.nui
echo "Running checkstyle..."
ant -logger org.apache.tools.ant.NoBannerLogger checkstyle
echo "- successful."