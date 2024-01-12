#!/bin/sh
./gradlew --parallel clean compileTest :key.ui:shadowJar :key.ui:distZip

if [ $? -gt 0 ]; then
  exit $?
fi

mkdir -p deployment/
#debugging for the start
ls -lR key.ui/build/distributions/*.zip key.ui/build/libs/key*exe.jar
mv key.ui/build/distributions/*.zip deployment/
mv key.ui/build/libs/key*exe.jar deployment/
