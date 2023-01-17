/*
 * @(#)AbstractTreeWriter.java	1.16 00/02/02
 *
 * Copyright 1998-2000 Sun Microsystems, Inc. All Rights Reserved.
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
 * Abstract class to print the class hierarchy page for all the Classes. This
 * is sub-classed by {@link PackageTreeWriter} and {@link TreeWriter} to
 * generate the Package Tree and global Tree(for all the classes and packages)
 * pages. 
 *
 * @author Atul M Dambalkar
 */
public abstract class AbstractTreeWriter extends HtmlStandardWriter {

    /**
     * The class and interface tree built by using {@link ClassTree}
     */
    protected final ClassTree classtree;

    /**
     * Constructor initilises classtree variable. This constructor will be used
     * while generating global tree file "overview-tree.html".
     * 
     * @param filename   File to be generated.
     * @param classtree  Tree built by {@link com.sun.tools.doclets.ClassTree}
     */
    protected AbstractTreeWriter(String filename, ClassTree classtree) 
                                 throws IOException, DocletAbortException {
        super(filename);
        this.classtree = classtree;
    }
    
    /**
     * Create appropriate directory for the package and also initilise the 
     * relative path from this generated file to the current or
     * the destination directory. This constructor will be used while 
     * generating "package tree" file.
     *
     * @param path Directories in this path will be created if they are not 
     * already there.
     * @param filename Name of the package tree file to be generated.
     * @classtree The tree built using {@link com.sun.tools.doclets.ClassTree}
     * for the package pkg.
     * @param pkg PackageDoc for which tree file will be generated.
     */
    protected AbstractTreeWriter(String path, String filename, 
                                 ClassTree classtree, PackageDoc pkg) 
                                 throws IOException, DocletAbortException {
        super(path, filename, DirectoryManager.getRelativePath(pkg.name()));
        this.classtree = classtree;
    }

    /**
     * Generate each level of the class tree. For each sub-class or 
     * sub-interface indents the next level information.
     * Recurses itself to generate subclasses info.
     * To iterate is human, to recurse is divine - L. Peter Deutsch.
     *
     * @param parent the superclass or superinterface of the list.
     * @param list list of the sub-classes at this level.
     */
    protected void generateLevelInfo(ClassDoc parent, List list) {
        if (list.size() > 0) {
            ul();
            for (int i = 0; i < list.size(); i++) {
                ClassDoc local = (ClassDoc)list.get(i);
                printPartialInfo(local);
                printExtendsImplements(parent, local);
                generateLevelInfo(local, classtree.subs(local));   // Recurse 
            }
            ulEnd();
        }
    }

    /**
     * Generate the heading for the tree depending upon tree type if it's a 
     * Class Tree or Interface tree and also print the tree.
     *
     * @param list List of classes which are at the most base level, all the 
     * other classes in this run will derive from these classes.
     * @param heading Heading for the tree.
     */
    protected void generateTree(List list, String heading) {
        if (list.size() > 0) {
            ClassDoc cd = (ClassDoc)list.get(0);   
            printTreeHeading(heading);
            generateLevelInfo(cd.isClass()? (ClassDoc)list.get(0): null, list);
        }
    }

    /**
     * Print the information regarding the classes which this class extends or
     * implements. 
     *
     * @param cd The classdoc under consideration.
     */
    protected void printExtendsImplements(ClassDoc parent, ClassDoc cd) {
        ClassDoc[] interfaces = cd.interfaces();
        if (interfaces.length > (cd.isInterface()? 1 : 0)) {
            Arrays.sort(interfaces);
            if (cd.isInterface()) {
                print(" (" + getText("doclet.also") + " extends ");
            } else {
                print(" (implements ");
            }
            boolean printcomma = false;
            for (int i = 0; i < interfaces.length; i++) {
                if (parent != interfaces[i]) {
                    if (printcomma) {
                        print(", ");
                    }
                    printPreQualifiedClassLink(interfaces[i]);
                    printcomma = true;
                }
            }
            println(")");
        }
    }

    /**
     * Print information about the class kind, if it's a "class" or "interface".
     *
     * @param cd classdoc.
     */
    protected void printPartialInfo(ClassDoc cd) {
        boolean isInterface = cd.isInterface();
        li("circle");
        print(isInterface? "interface " : "class ");
        printPreQualifiedBoldClassLink(cd);
    } 

    /**
     * Print the heading for the tree.
     * 
     * @param heading Heading for the tree.
     */
    protected void printTreeHeading(String heading) {
        h2();
        println(getText(heading));
        h2End();
    }

    /**
     * Highlight "Tree" word in the navigation bar, since this is the tree page.
     */
    protected void navLinkTree() {
        navCellRevStart();
        fontStyle("NavBarFont1Rev");
        boldText("doclet.Tree");
        fontEnd();
        navCellEnd();
    }              
}
