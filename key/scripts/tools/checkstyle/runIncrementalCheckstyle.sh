#!/bin/bash

cd `dirname $0`

HOME_DIR=`readlink -f ../../../..`
DIFF_FILE=$HOME_DIR/checkstyle-diff.txt

MERGE_BASE=`git merge-base HEAD origin/master`
OPTIONS=""

javac -cp checkstyle-7.6-all.jar -d . -sourcepath $HOME_DIR \
      GitDiffFilter.java \
      NoEmbeddedPlusPlusCheck.java

for arg in "$@"
do
  case $arg in
    --xml)
      OPTIONS="-f xml "
      ;;

    --base=*)
      MERGE_BASE=${arg#*=}
      ;;

    --out=*)
      OPTIONS="-o ${arg#*=}"
  esac
done

git diff -U0 $MERGE_BASE > $DIFF_FILE

# Uncomment the incremental check in the checkstyle configuration
sed -e 's/<!--KeY\(.*\)-->/\1/' key_checks.xml > key_checks_incremental.xml

java -ea -cp .:checkstyle-7.6-all.jar \
    -Dhome.dir=$HOME_DIR/ \
    -Ddiff.file=$DIFF_FILE \
    com.puppycrawl.tools.checkstyle.Main \
    -c key_checks_incremental.xml \
    $OPTIONS $HOME_DIR/key/key.core/src
