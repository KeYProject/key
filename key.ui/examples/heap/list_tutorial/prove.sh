#!/bin/sh -xe

keytop=../../../../

(cd $keytop ; pwd ; ./gradlew shadowJar)

pwd

java -cp $keytop/key.ui/build/libs/key-2.13.0-exe.jar:key-citool-1.6.0-mini.jar de.uka.ilkd.key.CheckerKt --proof-path proofs project.key 2>&1 | tee prove.log
