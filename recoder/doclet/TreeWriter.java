/*
 * @(#)TreeWriter.java	1.25 00/02/02
 *
 * Copyright 1997-2000 Sun Microsystems, Inc. All Rights Reserved.
 * 
 * This software is the proprietary information of Sun Microsystems, Inc.  
 * Use is subject to license terms.
 * 
 */



import com.sun.tools.doclets.*;
import com.sun.javadoc.*;
import java.io.*;
import java.lang.*;
import java.util.*;

/**
 * Generate Class Hierarchy page for all the Classes in this run.  Use
 * {@link com.sun.tools.doclets.ClassTree} for building the Tree. The name of 
 * the generated file is "overview-tree.html" and it is generated in the 
 * current or the destination directory. 
 *
 * @author Atul M Dambalkar
 */
public class TreeWriter extends AbstractTreeWriter {

    /**
     * Packages in this run.
     */
    private PackageDoc[] packages;

    /**
     * True if there are no packages specified on the command line, 
     * False otherwise.
     */
    private boolean classesonly;

    /**
     * Constructor to construct TreeWriter object.
     *
     * @param file String filename
     * @param classtree Tree built using
     * {@link com.sun.tools.doclets.ClassTree}.
     */
    public TreeWriter(String filename, ClassTree classtree)  
                                 throws IOException, DocletAbortException {
        super(filename, classtree);
        packages = Standard.configuration().packages;
	classesonly = packages.length == 0;
    }

    /** 
     * Create a TreeWriter object and use it to generate the
     * "overview-tree.html" file.
     *
     * @param classtree 
     * {@link com.sun.tools.doclets.ClassTree}.
     */ 
    public static void generate(ClassTree classtree) 
                                throws DocletAbortException {
        TreeWriter treegen;
        String filename = "overview-tree.html";
        try {
            treegen = new TreeWriter(filename, classtree); 
            treegen.generateTreeFile();
            treegen.close();
        } catch (IOException exc) {
            Standard.configuration().standardmessage.
                error("doclet.exception_encountered", exc.toString(), filename);
            throw new DocletAbortException();
        }
    }

    /**
     * Print the interface hierarchy and class hierarchy in the file.
     */
    public void generateTreeFile() throws IOException {
        printHeader(getText("doclet.Window_Class_Hierarchy",
                            Standard.configuration().windowtitle));
        printTreeHeader();

        printPageHeading();
    
        printPackageTreeLinks();

        generateTree(classtree.baseclasses(), "doclet.Class_Hierarchy"); 
        generateTree(classtree.baseinterfaces(), "doclet.Interface_Hierarchy"); 

        printTreeFooter();
    }

    /**
     * Generate the links to all the package tree files.
     */
    protected void printPackageTreeLinks() {
        if (!classesonly) {
            dl();
            dt();
            boldText("doclet.Package_Hierarchies");
            dd();
            for (int i = 0; i < packages.length; i++) {
                String filename = pathString(packages[i], "package-tree.html");
                printHyperLink(filename, "", packages[i].name());
                if (i < packages.length - 1) {
                    print(", ");
                }
            }
            dlEnd();
            hr();
        }
    }

    /**
     * Print the navigation bar links at the top.
     */
    protected void printTreeHeader() {
        navLinks(true);
        hr();
    } 

    /**
     * Print the navigation bar links at the bottom.
     */
    protected void printTreeFooter() {
        hr(); 
        navLinks(false);
        printBottom();
        printBodyHtmlEnd();
    } 

    /**
     * Print the page title "Hierarchy For All Packages" at the top of the tree
     * page.
     */
    protected void printPageHeading() {
        center();
        h2();
        printText("doclet.Hierarchy_For_All_Packages");
        h2End();
        centerEnd();
    }
}
