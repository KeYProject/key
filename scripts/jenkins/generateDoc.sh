#!/bin/sh -x
# API Doc generation to come
cd key
export GRADLE_OPTS="-Dorg.gradle.daemon=false"
./gradlew alldocJar
mkdir -p key/deployment
mv build/distribution/*.zip key/deployment

