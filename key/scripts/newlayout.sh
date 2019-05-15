#!/bin/sh

cat <<EOF
Welcome to the KeY newlayout script

!!! This script will change the directory of your current checkout.

!!! Ensure that your working copy is comitted!

!!! No waranty for data lost.

EOF

if [ ! -d key.core ]; then
    echo -e "\e[31mTHIS SCRIPT SHOULD BE RUN INSIDE key/key DIRECTORY!\e[0m. ABORT"
    exit 1
fi


require_clean_work_tree () {
    # Update the index
    git update-index -q --ignore-submodules --refresh
    err=0

    # Disallow unstaged changes in the working tree
    if ! git diff-files --quiet --ignore-submodules --
    then
        echo >&2 "cannot $1: you have unstaged changes."
        git diff-files --name-status -r --ignore-submodules -- >&2
        err=1
    fi

    # Disallow uncommitted changes in the index
    if ! git diff-index --cached --quiet HEAD --ignore-submodules --
    then
        echo >&2 "cannot $1: your index contains uncommitted changes."
        git diff-index --cached --name-status -r --ignore-submodules HEAD -- >&2
        err=1
    fi

    if [ $err = 1 ]
    then
        echo -e "You have uncomitted changes."
        echo -e "\e[33mPlease commit or stash them.\e[0m"
        exit 1
    fi
}

require_clean_work_tree

echo "Create src/*/*/* folders"
GITMV="git mv -k -v"
MKDIR="mkdir -pv"

for i in key.{core,ui,util,removegenerics,core.testgen,core.symbolic_execution,core.proof_references}/
do
    #intermediate storage of src
    $GITMV $i/src $i/tmp

    $MKDIR $i/src/main/
    $GITMV $i/tmp $i/src/main/java
    $GITMV $i/resources $i/src/main/
    $GITMV $i/META-INF $i/src/main/resources

    read
done

function merge_test() {
    $MKDIR $1/src/test/
    echo "Move $1.test/src to $1/src/test/java"
    $GITMV -f $1.test/src/      $1/src/test/java

    echo "Move $1.test/resources to $1/src/test/resources"
    $GITMV -f $1.test/resources $1/src/test/resources
    $GITMV -f $1.test/META-INF  $1/src/test/resources/
}

echo -e <<EOF
!!! \e[31mHINT:
!!! \tSometimes the git command failes due to empty folder.
!!! \e[32mDO NOT WOORY! It is fine.\e[0m
EOF

merge_test key.core.testgen
merge_test key.core.symbolic_execution
merge_test key.core.proof_references
merge_test key.removegenerics
merge_test key.util
merge_test key.core


echo "Special treatment for tacletProofs"
$GITMV key.core{.test,}/tacletProofs


echo "Remove *.test projects"
function remove_project() {
    echo "Safe deletion of $1"
    #known files safe to delete!
    rm -rf $1/build.{gradle,xml} $1/testresults $1/runallproofs_tmp $1/bin $1/.??* $1/lib
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
        $MKDIR $dest
        $GITMV $f $dest
    done
    cd $owd
}

extract_antlr key.core/src/main
extract_antlr key.core/src/test

echo "Extract JavaCC"
owd=$(pwd)
(cd key.core/src/main;
 mkdir -p javacc/de/uka/ilkd/key/parser/{proof,schema}java/
 $GITMV ./java/de/uka/ilkd/key/parser/proofjava/ProofJavaParser.jj \
        javacc/de/uka/ilkd/key/parser/proofjava/;
 $GITMV ./java/de/uka/ilkd/key/parser/proofjava/Token.java.source \
        javacc/de/uka/ilkd/key/parser/proofjava/Token.java;
 $GITMV ./java/de/uka/ilkd/key/parser/schemajava/SchemaJavaParser.jj \
        javacc/de/uka/ilkd/key/parser/schemajava/;
 $GITMV  ./java/de/uka/ilkd/key/parser/schemajava/Token.java.source \
         javacc/de/uka/ilkd/key/parser/schemajava/Token.java;
)

for i in key.{core,ui,util,removegenerics,core.testgen,core.symbolic_execution,core.proof_references}
do
    git add -v $i/src
done

git add key.core/tacletProofs/


echo -e "\e[33mYou sould make a commit now.\e[0m"
echo -e "\t git commit -a "
