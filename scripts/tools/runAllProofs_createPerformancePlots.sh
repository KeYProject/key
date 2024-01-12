#!/bin/sh

#
# RunAllProofs documentation can be found at: key/doc/README.runAllProofs
#

LIST_TESTS_FLAG=--list-tests
HELP_FLAG=--help
RELOAD_ENABLED_FLAG=--reload-enabled
FORK_MODE_FLAG=--fork-mode
VERBOSE_FLAG=--verbose

list_help() {
    echo "Usage: runAllProofs [$HELP_FLAG] | [$LIST_TESTS_FLAG] |"
    echo "                                     [ [$RELOAD_ENABLED_FLAG=<true|false>]"
    echo "                                       [$VERBOSE_FLAG]"
    echo "                                       [$FORK_MODE_FLAG=<perFile|perGroup|noFork>]"
    echo "                                       [<groupNames>] ]"
    echo "Examples: runAllProofs $FORK_MODE_FLAG=perFile newBook comprehensions"
    echo "          runAllProofs $LIST_TESTS_FLAG"
}

resolve_symlink() {
   TARGET=`ls -l "$1"| awk '/\ ->\ /{print $NF}'`

   if [ -n "$TARGET" ] ; then
      RESULT="$TARGET"
      case "$RESULT" in
         /*) break ;;				# absolute symlink
         *)  RESULT=`dirname "$0"`/"$RESULT" ;;	# relative symlink
      esac
   else
      RESULT=$1
   fi

   echo "$RESULT"
}

SCRIPTLOCATION=`resolve_symlink "$0"`
SCRIPTFOLDER=`dirname $SCRIPTLOCATION`/..

#
# Parse command line parameters
#

JAVA_ARGS=""

while [ "$#" -ne 0 ]
    do
    case $1 in
      --fork-mode=*)
        FORK_MODE=$(echo $1 | cut -d'=' -f 2)
        JAVA_ARGS="$JAVA_ARGS -Dkey.runallproofs.forkMode=$FORK_MODE"
        shift
        continue
        ;;
      $RELOAD_ENABLED_FLAG=*)
        RELOAD_ENABLED=$(echo $1 | cut -d'=' -f 2)
        JAVA_ARGS="$JAVA_ARGS -Dkey.runallproofs.reloadEnabled=$RELOAD_ENABLED"
        shift
        continue
        ;;
      $VERBOSE_FLAG)
        JAVA_ARGS="$JAVA_ARGS -Dkey.runallproofs.verboseOutput=true"
        shift
        continue
        ;;
      -D*)
        JAVA_ARGS="$JAVA_ARGS $1"
        shift
        continue
        ;;
      $LIST_TESTS_FLAG)
        $SCRIPTFOLDER/tools/testRunner.sh de.uka.ilkd.key.proof.runallproofs.ListRunAllProofsTestCases
        exit
        ;;
      -h|-?|$HELP_FLAG)
        list_help
        exit
        ;;
      -*)
        echo Unrecognised option: $1
        exit
        ;;
      *)
        break
        ;;
    esac
    done

#
# Optionally, retrieve names of selected test cases
#

if [ "$#" -ne 0 ]
    then
    TEST_CASES=$1
    shift
    while [ "$#" -ne 0 ]
        do
        TEST_CASES="$TEST_CASES,$1"
        shift
        done
    JAVA_ARGS="$JAVA_ARGS -Dkey.runallproofs.testCases=$TEST_CASES"
fi

#
# Run JUnit
#

$SCRIPTFOLDER/tools/testRunner.sh $JAVA_ARGS org.junit.runner.JUnitCore de.uka.ilkd.key.proof.runallproofs.performance.RunAllProofsProfilingSuite
