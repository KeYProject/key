#!/bin/sh
cd key/
export GRADLE_OPTS="-Dorg.gradle.daemon=false"
./gradlew --parallel compileTest :key.ui:shadowJar :key.ui:distZip

mkdir -p key/deployment/

#debugging for the start
ls -lR key.ui/build/

mv key.ui/build/distributions/*.zip key/deployment/
mv key.ui/build/libs/key*exe.jar key/deployment/
