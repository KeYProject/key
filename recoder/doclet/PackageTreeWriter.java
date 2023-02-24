/*
 * @(#)PackageTreeWriter.java	1.14 00/02/02
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
 * Class to generate Tree page for a package. The name of the file generated is
 * "package-tree.html" and it is generated in the respective package directory.
 *
 * @author Atul M Dambalkar
 */
public class PackageTreeWriter extends AbstractTreeWriter {

    /**
     * Package for which tree is to be generated.
     */
    protected PackageDoc packagedoc;

    /**
     * The previous package name in the alpha-order list.
     */
    protected PackageDoc prev;

    /**
     * The next package name in the alpha-order list.
     */
    protected PackageDoc next;

    /**
     * Constructor.
     */
    public PackageTreeWriter(String path, String filename, 
                             PackageDoc packagedoc, 
                             PackageDoc prev, PackageDoc next,
                             boolean noDeprecated) 
                      throws IOException, DocletAbortException {
        super(path, filename, 
              new ClassTree(packagedoc.allClasses(), noDeprecated), packagedoc);
        this.packagedoc = packagedoc;
        this.prev = prev;
        this.next = next;
    }

    /**
     * Construct a PackageTreeWriter object and then use it to generate the 
     * package tree page.
     *
     * @param pkg      Package for which tree file is to be generated.
     * @param prev     Previous package in the alpha-ordered list.
     * @param next     Next package in the alpha-ordered list.
     * @param noDeprecated  If true, do not generate any information for 
     * deprecated classe or interfaces.
     */
    public static void generate(PackageDoc pkg, PackageDoc prev,
                                PackageDoc next, boolean noDeprecated)
                         throws DocletAbortException {
        PackageTreeWriter packgen;
        String path = DirectoryManager.getDirectoryPath(pkg);
        String filename = "package-tree.html";
        try {
            packgen = new PackageTreeWriter(path, filename, pkg, 
                                            prev, next, noDeprecated);
            packgen.generatePackageTreeFile();
            packgen.close();
        } catch (IOException exc) {
            Standard.configuration().standardmessage.
                error("doclet.exception_encountered", 
                       exc.toString(), filename);
            throw new DocletAbortException();
        }
    }

    /**
     * Generate a separate tree file for each package.
     */
    protected void generatePackageTreeFile() throws IOException {
        printHeader(getText("doclet.Window_Package_Class_Hierarchy", 
                             Standard.configuration().windowtitle,
                             packagedoc.name()));
        printPackageTreeHeader();

        if (Standard.configuration().packages.length > 1) {
            printLinkToMainTree();
        }

        generateTree(classtree.baseclasses(), "doclet.Class_Hierarchy"); 
        generateTree(classtree.baseinterfaces(), "doclet.Interface_Hierarchy"); 

        printPackageTreeFooter();
        printBottom();
        printBodyHtmlEnd();
    }

    /**
     * Print the navigation bar header for the package tree file.
     */
    protected void printPackageTreeHeader() {
        navLinks(true);
        hr();
        center();
        h2(getText("doclet.Hierarchy_For_Package", packagedoc.name()));
        centerEnd();
    }

    /**
     * Generate a link to the tree for all the packages.
     */
    protected void printLinkToMainTree() {
        dl();
        dt();
        boldText("doclet.Package_Hierarchies");
        dd();
        navLinkMainTree(getText("doclet.All_Packages"));
        dlEnd();
        hr();
    } 

    /**
     * Print the navigation bar footer for the package tree file.
     */
    protected void printPackageTreeFooter() {
        hr();
        navLinks(false);
    }

    /**
     * Link for the previous package tree file.
     */ 
    protected void navLinkPrevious() {
        if (prev == null) {
            navLinkPrevious(null);
        } else {
            String path = DirectoryManager.getRelativePath(packagedoc.name(),
                                                           prev.name());
            navLinkPrevious(path + "package-tree.html");
        }
    }
    
    /**
     * Link for the next package tree file.
     */ 
    protected void navLinkNext() {
        if (next == null) {
            navLinkNext(null);
        } else {
            String path = DirectoryManager.getRelativePath(packagedoc.name(),
                                                           next.name());
            navLinkNext(path + "package-tree.html");
        }
    }

    /**
     * Link to the package summary page for the package of this tree.
     */
    protected void navLinkPackage() {
        navCellStart();
        printHyperLink("package-summary.html", "", getText("doclet.Package"),
                        true, "NavBarFont1");
        navCellEnd();
    }
}
