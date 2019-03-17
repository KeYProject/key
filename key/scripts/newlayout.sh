#!/bin/sh

echo "Create src/*/*/* folders"

for i in key.{core,ui,util,removegenerics,core.testgen,core.symbolic_execution,core.proof_references}/
do
    git mv -k $i/src $i/tmp

    echo "Create new java source folder: $i/src/main/"
    mkdir -p $i/src/main/

    git mv -k $i/tmp $i/src/main/java
    git mv -k $i/resources $i/src/main/
    git mv -k $i/META-INF $i/src/main/resources
done

function merge_test() {
    mkdir $1/src/test/
    echo "Move $1.test to $1"
    git mv -kf $1.test/src/      $1/src/test/java
    git mv -kf $1.test/resources $1/src/test/resources
 #   git mv $1.test/META-INF  $1/src/test/resources/
}

echo
echo "!!! HINT: Sometimes the git command failes due to empty folder. (removegenerics.test, ui.test)"
echo "!!! DO NOT WOORY! It is fine."
echo

merge_test key.core.testgen
merge_test key.core.symbolic_execution
merge_test key.core.proof_references
merge_test key.removegenerics
merge_test key.util
merge_test key.core


echo "Special treatment for tacletProofs"
git mv -k key.core{.test,}/tacletProofs


echo "Remove *.test projects"
function remove_project() {
    echo "Safe deletion of $1"
    #known files safe to delete!
    rm -rf $1/build.{gradle,xml} $1/testresults $1/runallproofs_tmp $1/bin $1/.* $1/lib
    rm -ri $1
}


remove_project  key.core.testgen.test
remove_project  key.core.symbolic_execution.test
remove_project  key.core.proof_references.test
remove_project  key.removegenerics.test
remove_project  key.util.test
remove_project  key.core.test


function extract_antlr() {
    echo "Extract ANTLR in $1"
    owd=$(pwd)
    cd $1
    find java -iname '*.g' | while read f; do
        a=$(dirname $f)
        dest=antlr/${a##java/}
        mkdir -p $dest
        git mv -k $f $dest
    done
    cd $owd
}

extract_antlr key.core/src/main
extract_antlr key.core/src/test

echo "Extract JavaCC"
owd=$(pwd)
cd key.core/src/main
mkdir -p javacc/de/uka/ilkd/key/parser/{proof,schema}java/

git mv ./java/de/uka/ilkd/key/parser/proofjava/ProofJavaParser.jj \
    javacc/de/uka/ilkd/key/parser/proofjava/

git mv ./java/de/uka/ilkd/key/parser/proofjava/Token.java.source \
    javacc/de/uka/ilkd/key/parser/proofjava/Token.java

git mv ./java/de/uka/ilkd/key/parser/schemajava/SchemaJavaParser.jj \
    javacc/de/uka/ilkd/key/parser/schemajava/

git mv ./java/de/uka/ilkd/key/parser/schemajava/Token.java.source \
    javacc/de/uka/ilkd/key/parser/schemajava/Token.java
