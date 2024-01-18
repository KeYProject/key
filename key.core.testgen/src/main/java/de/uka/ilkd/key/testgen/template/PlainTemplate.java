package de.uka.ilkd.key.testgen.template;

import static de.uka.ilkd.key.testgen.template.Constants.OBJENESIS_NAME;

public class PlainTemplate implements Template {
    @Override
    public String shCompileWithOpenJML() {
        return """
                #!/bin/bash
                        
                if [ -e "openjml.jar" ]; then
                   java -jar openjml.jar -cp "." -rac *.java
                 else
                    echo "openjml.jar not found!"
                    echo "Download openJML from http://sourceforge.net/projects/jmlspecs/files/"%s
                    echo "Copy openjml.jar into the directory with test files."
                """;
    }

    @Override
    public String shCompileWithOpenJML(String openJMLPath, String objenesisPath) {
        return """
                #!/bin/bash
                if [ -e %s/openjml.jar ]; then
                    if [ -e %s ]; then
                        java -jar openJMLPath/openjml.jar -cp "." %s + " -rac *"
                    JAVA_FILE_EXTENSION_WITH_DOT + NEW_LINE + "   else" + NEW_LINE
                    echo "objenesis-2.2.jar not found!
                    fi
                else
                   echo "openjml.jar not found!"
                   echo "Download openJML from http://sourceforge.net/projects/jmlspecs/files/"
                   echo "Copy openjml.jar into the directory with test files."
                fi""".formatted(
                openJMLPath, objenesisPath, objenesisPath + "/" + OBJENESIS_NAME);
    }


    @Override
    public String shExecuteWithOpenJML(String path, String objenesisPath) {
        return """
                #!/bin/bash
                if [ ! -e path/jmlruntime.jar ]; then
                    echo "jmlruntime.jar not found!"
                    echo "Download openJML from http://sourceforge.net/projects/jmlspecs/files/""
                    echo "Copy jmlruntime.jar into the directory with test files.""
                    exit 1
                fi

                if [ ! -e path/jmlspecs.jar" ]; then
                    echo "jmlspecs.jar not found!"
                    echo "Download openJML from http://sourceforge.net/projects/jmlspecs/files/"
                    echo "Copy jmlspecs.jar into the directory with test files."
                    exit 2
                fi
                               
                if [ ! -e "" + objenesisPath/OBJENESIS_NAME ]; then
                    echo "objenesis-2.2.jar not found!"                
                    exit 3
                fi
                               
                               
                if [ "$1" = "" ] ; then
                    echo "Provide the test driver as an argument (without + JAVA_FILE_EXTENSION_WITH_DOT + " postfix). For example:"" + NEW_LINE
                    echo "  executeWithOpenJML.sh TestGeneric0 "
                    echo "Make sure that jmlruntime.jar and jmlspecs.jar are in the""
                    echo "current directory."
                    exit 4
                fi 
                               
                java -cp " + objenesisPath/OBJENESIS_NAME + ":" + path / "jmlruntime.jar:"/ "jmlspecs.jar:. $1
                 """;
    }

}
