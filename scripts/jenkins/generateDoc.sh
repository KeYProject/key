#!/bin/sh -x
# API Doc generation to come
export GRADLE_OPTS="-Dorg.gradle.daemon=false"
./gradlew alldocJar
mkdir -p deployment
mv build/distribution/*.zip deployment

