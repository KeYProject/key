#!/bin/bash

HOME_DIR=../../../../
DIFF_FILE=$HOME_DIR/checkstyle-diff.txt

cd `dirname $0`

MERGE_BASE=`git merge-base HEAD origin/master`
OPTIONS=""

for arg in "$@"
do
  case $arg in
    --xml)
      OPTIONS="-f xml -o HOME_DIR/checkstyle-results.xml"
      ;;

    --base=*)
      MERGE_BASE=${arg#*=}
      ;;
  esac
done

git diff -U0 $MERGE_BASE > $DIFF_FILE

#java -ea -Dprefix=../../../ -cp .:checkstyle-7.6-all.jar -Xdebug -Xnoagent -Djava.compiler=NONE -Xrunjdwp:transport=dt_socket,server=y,suspend=n,address=1234  com.puppycrawl.tools.checkstyle.Main -c key_checks.xml -f xml ../../key.core/src

java -ea -Dprefix=$HOME_DIR -cp .:checkstyle-7.6-all.jar com.puppycrawl.tools.checkstyle.Main -c key_checks.xml $OPTIONS $HOME_DIR/key/key.core/src
