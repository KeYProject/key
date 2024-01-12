#!/bin/sh

#
# CLI for running KeY JUnit test cases manually.
# Used by key/core/scripts/runAllProofs and key/core/scripts/proveRules
# Usage example: testRunner.sh -D... org.junit.runner.JUnitCore package.to.KeYTestClass
#

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

#
# Determine JAVA_HOME
#

UNAME=`uname -s 2>/dev/null | tr '[:upper:]' '[:lower:]'`
ARCH=`uname -pm 2>/dev/null | tr '[:upper:]' '[:lower:]' | tr ' ' '-'`

if [ -z "$JAVA_HOME" ] ; then
    JAVA=`which java`
    if [ -z "$JAVA" ] ; then
	echo "Cannot find JAVA. Please set your PATH or \$JAVA_HOME."
	exit 1
    fi
else
    echo "Using JDK installation from:      $JAVA_HOME"
    if [ "$UNAME" = "darwin" ] ; then
	JRE=$JAVA_HOME/Home
	JAVA=$JRE/bin/java
    # other OS
    else
	JRE=$JAVA_HOME/jre
	JAVA=$JRE/bin/java
    fi
fi

#
# Determining KEY_HOME
#

if [ -z "$KEY_HOME" ] ; then
   KEY_HOME=`resolve_symlink "$0"`	# resolve symlink name (points to key/scripts/tools/testRunner.sh)
   KEY_HOME=`dirname "$KEY_HOME"`	# strip executable filename (points to key/scripts/tools/)
   KEY_HOME=`cd "$KEY_HOME";pwd`	# and now expand the path to full path (absolute path)
   KEY_HOME=`dirname "$KEY_HOME"`	# strip tools/ directory (points to key/scripts)
   KEY_HOME=`dirname "$KEY_HOME"`	# strip scripts/ directory (points to key/)
fi
# echo "Using KeY installation from:      $KEY_HOME"

KEY_LIB="$KEY_HOME/key.core/lib"

#
# KeY CLASSPATH
#

key_ext_jars="antlr.jar recoderKey.jar"

keyclasspath="$KEY_HOME/key.core/bin:$KEY_HOME/key.ui/bin:$KEY_HOME/key.util/bin:$KEY_HOME/key.core.proof_reference/bin:$KEY_HOME/key.core.symbolic_execution/bin:$KEY_HOME/key.core.testgen/bin:$KEY_HOME/key.core.test/bin"

for i in $key_ext_jars ; do
    current_jar="$KEY_LIB/$i"
    if [ ! -f "$current_jar" ]
    then
       echo Cannot find $current_jar.
       echo Copy or link the file into the
       echo $KEY_LIB directory.
       exit 1
    else
       keyclasspath="${keyclasspath}:$current_jar"
    fi
done

KEY_LIB_JUNIT="$KEY_HOME/key.util.test/lib"

key_junit_jars="hamcrest-core-1.3.jar  junit-4.12.jar"

for i in $key_junit_jars ; do
    current_jar="$KEY_LIB_JUNIT/$i"
    if [ ! -f "$current_jar" ]
    then
       echo Cannot find $current_jar.
       echo Copy or link the file into the
       echo $KEY_LIB_JUNIT directory.
       exit 1
    else
       keyclasspath="${keyclasspath}:$current_jar"
    fi
done

#
# Run Java
#

$JAVA -ea:de.uka.ilkd.key...\
-noverify\
-Djvm.dir=$JVM_DIR\
-Xms64m -Xmx2048m \
-Dkey.home="$KEY_HOME" \
-classpath "$keyclasspath" \
"$@"

