// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util.removegenerics;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.util.removegenerics.monitor.ConsoleGenericRemoverMonitor;

/**
 * That's the entry point when the transformation is to be applied outside from
 * the KeY-tool.
 * 
 * It contains only static methods and {@link #main(String[])} is the one
 * entry-point.
 * 
 * The following parameters are supported:
 * <dl>
 * <dt>-cp or -classpath</dt>
 * <dd>Set a location to look for .java or .class files</dd>
 * <dt>-d</dt>
 * <dd>Set the output directory. Files will be placed according to their
 * package</dd>
 * <dt>-v</dt>
 * <dd>be verbose with the output. lots of internal information will pop up.</dd>
 * <dt><i>file name</i></dt>
 * <dd>add a .java-file to examine</dd>
 * <dt><i>directory name</i></dt>
 * <dd>add a directory to examine. every .java within the named directory tree
 * will be considered</dd>
 * <dt>@<i>filename</i></dt>
 *      <dd>take every line of the file <i>filename</i> and add it as a file
 *      to consider</dd>
 *      <dt>jar file name</dt>
 *      <dd>add a jar-file to examine. every .java file within the
 *      jar-repository will be considered</dd>
 *      </dl>
 * 
 * All considered java source files are parsed in. If needed, source or class
 * files will be searched for in the specified -cp files, repositories and
 * directories.
 * 
 * Generics are removed and the result is written to the output directory ('.'
 * by default).
 * 
 * @author MU
 * 
 */
public class Main {
    // hide constructor
    private Main() {
    }

    /**
     * @param args
     * @throws Exception if something goes wrong like opening a file etc.
     */
    public static void main(String[] args) throws Exception {

        System.out.println("Version - 071019 - 1546");

        if (args.length == 0)
            usage();

        GenericRemover remover = new GenericRemover(new ConsoleGenericRemoverMonitor());
        for (int i = 0; i < args.length; i++) {

            try {
                if (args[i].equals("-d")) {
                   remover.setOutDir(new File(args[++i].trim()));
                } else if (args[i].equals("-classpath") || args[i].equals("-cp")) {
                    for (String s : args[++i].split(File.pathSeparator)) {
                       remover.addSearchPath(s);
                    }
                } else if (args[i].startsWith("@")) {
                    List<String> files = addLinesFromFile(args[i].substring(1));
                    remover.addSourceFiles(files);
                } else if (args[i].equals("-v")) {
                    GenericResolutionTransformation.DEBUG_OUTPUT = true;
                } else {
                    remover.addSourceFile(args[i]);
                }
            } catch (IndexOutOfBoundsException e) {
                System.err.println("Argument " + args[i - 1] + " needs a parameter");
            }

        }

        if (!remover.getOutDir().exists()) {
            System.err.println("The output directory does not exist");
            System.exit(1);
        }
        
        remover.removeGenerics();
    }

    private static void usage() {
        System.out.println("This program can be used to transform a Java program with generics into one without.");
        System.out.println();
        System.out.println("The following arguments are supported");
        System.out.println("   -cp or -classpath ");
        System.out.println("     Set a location to look for .java or .class files");
        System.out.println("   -d");
        System.out.println("     Set the output directory. Files will be placed according to their package");
        System.out.println("   -v");
        System.out.println("     be verbose with the output. lots of internal information will pop up.");
        System.out.println("   <file-name>");
        System.out.println("     add a .java-source file to examine");
        System.out.println("   <directory-name>");
        System.out.println("     add a directory to examine. every .java within the named directory tree will be considered");
        System.out.println("   @filename");
        System.out.println("     take every line of the file filename and add it as a file to consider");
        System.out.println("   <jar-file-name>");
        System.out.println("     add a jar-file to examine. every .java file within the jar-repository will be considered");
        System.out.println();
        System.exit(0);
    }

    private static List<String> addLinesFromFile(String file) throws IOException {
        List<String> files = new LinkedList<String>();
        BufferedReader br = new BufferedReader(new FileReader(file));

        String line = br.readLine();
        while (line != null) {
            line = line.trim();
            if (!line.startsWith("#"))
                files.add(line);
        }
        br.close();
        return files;
    }
}