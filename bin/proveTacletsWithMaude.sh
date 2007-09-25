#!/bin/sh

resolve_symlink  ()
{ 
   TARGET=`ls -l $1| awk '/\ ->\ /{print $NF}'`

   if [ -n "$TARGET" ] ; then
      RESULT="$TARGET"
      case "$RESULT" in
         /*) break ;;				# absolute symlink
         *)  RESULT=`dirname $0`/"$RESULT" ;;	# relative symlink
      esac
   else
      RESULT=$1
   fi

   echo "$RESULT"
}

MAUDE=maude
MAUDE_HOME=`which maude`
MAUDE_HOME=`resolve_symlink "$MAUDE_HOME"`	# resolve symlink name
MAUDE_HOME=`dirname $MAUDE_HOME`	# strip executable filename
if [ -z "$KEY_HOME" ] ; then
   KEY_HOME=`resolve_symlink "$0"`	# resolve symlink name
   KEY_HOME=`dirname $KEY_HOME`		# strip executable filename
   KEY_HOME=`cd "$KEY_HOME";pwd`	# and now expand the path to full
   KEY_HOME=`dirname $KEY_HOME`		# strip bin/ sirectory
fi
RESOURCES_PATH=$KEY_HOME/system/resources/de/uka/ilkd/key/proof/rules/
MAUDE_LIB=$MAUDE_HOME:$RESOURCES_PATH
export MAUDE_LIB
echo Using Maude installation from: $MAUDE_HOME
echo Using Maude input from:        $MAUDE_LIB
echo Using KeY installation from:   $KEY_HOME
echo [Generating Maude Input]
$KEY_HOME/bin/runJava de/uka/ilkd/key/rule/CheckPrgTransfSoundness testTacletsInput.maude >maudeInputGeneration.log
echo [Running Maude...]
cat $RESOURCES_PATH/loadTestTaclet | $MAUDE > testTacletsOutput.maude 2> maudeWarnings.txt 

S1=`grep 'ResultingBoolVal:\[Bool\] -->' testTacletsOutput.maude | grep -v 'ResultingBoolVal:\[Bool\] --> true' `
if [ "$S1\n" = "\n" ] ; then 
  S1=`diff maudeWarnings.txt $RESOURCES_PATH/normalMaudeWarnings.txt`
  if [ "$S1" = "" ] ; then
      rm maudeWarnings.txt
      rm testTacletsInput.maude
      rm testTacletsOutput.maude
      rm maudeInputGeneration.log
      echo "Maude Taclet Check OK"
      exit
  fi
fi
echo "Something wrong in the test for taclet correctness with Maude, see testTacletsInput.maude, testTacletsOutput.maude, maudeInputGeneration.log, and maudeWarnings.txt"
exit 1
