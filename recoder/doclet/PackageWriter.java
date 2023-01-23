/*
 * @(#)PackageWriter.java	1.35 00/02/02
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
 * Class to generate file for each package contents in the right-hand 
 * frame. This will list all the Class Kinds in the package. A click on any
 * class-kind will update the frame with the clicked class-kind page.
 *
 * @author Atul M Dambalkar
 */
public class PackageWriter extends AbstractPackageWriter {

    /** 
     * The prev package name in the alpha-order list.
     */
    protected PackageDoc prev;

    /** 
     * The next package name in the alpha-order list.
     */
    protected PackageDoc next;

    /**
     * Constructor to construct PackageWriter object and to generate 
     * "package-summary.html" file in the respective package directory. 
     * For example for package "java.lang" this will generate file 
     * "package-summary.html" file in the "java/lang" directory. It will also 
     * create "java/lang" directory in the current or the destination directory
     * if it doesen't exist.
     *
     * @param path Directories in this path will be created if they are not 
     * already there.
     * @param filename Name of the package summary file to be generated, 
     * "package-frame.html".
     * @param packagedoc PackageDoc under consideration.
     * @param prev Previous package in the sorted array.
     * @param next Next package in the sorted array.
     */
    public PackageWriter(String path, String filename, PackageDoc packagedoc,
                         PackageDoc prev, PackageDoc next) 
                         throws IOException, DocletAbortException {
        super(path, filename, packagedoc);
        this.prev = prev;
        this.next = next;
    }

    /**
     * Generate a package summary page for the right-hand frame. Construct
     * the PackageFrameWriter object and then uses it generate the file.
     *
     * @param pkg The package for which "pacakge-summary.html" is to be
     * generated.
     * @param prev Previous package in the sorted array.
     * @param next Next package in the sorted array.
     */
    public static void generate(PackageDoc pkg, PackageDoc prev,
                                PackageDoc next) throws DocletAbortException {
        PackageWriter packgen;
        String path = DirectoryManager.getDirectoryPath(pkg);
        String filename = "package-summary.html";
        try {
            packgen = new PackageWriter(path, filename, pkg, prev, next);
            packgen.generatePackageFile();
            packgen.close();
            packgen.copyDocFiles(path);
        } catch (IOException exc) {
            Standard.configuration().standardmessage.
                error("doclet.exception_encountered", exc.toString(), filename);
            throw new DocletAbortException();
        }
    }

    /**
     * Generate class listing for all the classes in this package. Divide class
     * listing as per the class kind and generate separate listing for 
     * Classes, Interfaces, Exceptions and Errors.
     */
    protected void generateClassListing() {
        generateClassKindListing(packagedoc.interfaces(), 
                                 getText("doclet.Interface_Summary"));
        generateClassKindListing(packagedoc.ordinaryClasses(),
                                 getText("doclet.Class_Summary"));
        generateClassKindListing(packagedoc.exceptions(),
                                 getText("doclet.Exception_Summary"));
        generateClassKindListing(packagedoc.errors(),
                                 getText("doclet.Error_Summary"));
    }
    
    /** 
     * Generate specific class kind listing. Also add label to the listing.
     *
     * @param arr Array of specific class kinds, namely Class or Interface or
     * Exception or Error.
     * @param label Label for the listing
     */
    protected void generateClassKindListing(ClassDoc[] arr, String label) {
        if(arr.length > 0) {
            Arrays.sort(arr);    
            tableIndexSummary();
            printFirstRow(label);
            for (int i = 0; i < arr.length; i++) {
                boolean deprecated = arr[i].tags("deprecated").length > 0;
                if (!Util.isCoreClass(arr[i]) || !isGeneratedDoc(arr[i])) {
                    continue;
                }
                trBgcolorStyle("white", "TableRowColor");
                summaryRow(15);
                bold();
                printClassLinkForSameDir(arr[i]);
                boldEnd();
                summaryRowEnd();
                summaryRow(0);
                if (deprecated) {
                    boldText("doclet.Deprecated");
                    space();
                    printSummaryDeprecatedComment(
                                              arr[i].tags("deprecated")[0]);
                } else {
                    printSummaryComment(arr[i]);
                }
                summaryRowEnd();
                trEnd();
            }
            tableEnd();
            println("&nbsp;");
            p();
        }
    }

    /**
     * Print the table heading for the class-listing.
     *
     * @param label Label for the Class kind listing.
     */
    protected void printFirstRow(String label) {
        tableHeaderStart("#CCCCFF");
        bold(label);
        tableHeaderEnd();
    }

    /**
     * Print the package comment as specified in the "packages.html" file in 
     * the source package directory.
     */
    protected void printPackageComment() {
        if (packagedoc.inlineTags().length > 0) {
            anchor("package_description");
            h2(getText("doclet.Package_Description", packagedoc.name()));
            p();
            printInlineComment(packagedoc);
            p();
        }
    }
   
    /**
     * Print the package description and the tag information from the
     * "packages.html" file.
     */ 
    protected void printPackageDescription() throws IOException {
        printPackageComment();
        generateTagInfo(packagedoc);
    }
    
    /**
     * Print one line summary cooment for the package at the top of the page and
     * add link to the description which is generated at the end of the page.
     *
     * @param heading Package name.
     */                            
    protected void printPackageHeader(String heading) {
        navLinks(true);
        hr();
        h2(getText("doclet.Package") + " " + heading);
        if (packagedoc.inlineTags().length > 0) {
            printSummaryComment(packagedoc);
            p();
            bold(getText("doclet.See"));
            br();
            printNbsps();
            printHyperLink("", "package_description",
                           getText("doclet.Description"), true);
            p();
        }
    }   

    /**
     * Print the navigation bar links at the bottom also print the "-bottom"
     * if specified on the command line.
     */                            
    protected void printPackageFooter() {
        hr();
        navLinks(false);
        printBottom();
    }

    /**
     * Copy the "doc-files" directory contents from the source package directory
     * to the generated documentation directory. For example for a package 
     * java.lang this method find out the source location of the package using
     * {@link SourcePath} and if "doc-files" directory is found in the source
     * directory structure, copy the entire directory, to the generated 
     * documentation hierarchy.
     *
     * @param path The sourcepath.
     */
    protected void copyDocFiles(String path) throws DocletAbortException {
        SourcePath sourcePath = new SourcePath(
                                  Standard.configuration().sourcepath);
        String docfilesdir = path + fileseparator + "doc-files";
        File sourcedir = sourcePath.getDirectory(docfilesdir);
        if (sourcedir == null) {
            return;
        }
        String destname = destdir;
        if (destname.length() > 0 && !destname.endsWith(fileseparator)) {
            destname += fileseparator;      
        }
        String src = sourcedir.toString();
        String dest = destname + path + fileseparator + "doc-files";
        try {
            File srcdir = new File(src);
            File destdir = new File(dest);
            DirectoryManager.createDirectory(dest);
            String[] files = srcdir.list();
            for (int i = 0; i < files.length; i++) {
                File srcfile = new File(srcdir, files[i]);
                File destfile = new File(destdir, files[i]);
                if (srcfile.isFile()) {
                    notice("doclet.Copying_File_0_To_Dir_1", 
                            srcfile.toString(), destdir.toString());
                    Util.copyFile(destfile, srcfile); 
                }
            }
        } catch (SecurityException exc) {
            throw new DocletAbortException();
        } catch (IOException exc) {
            throw new DocletAbortException();
        }
    }
                
    /**
     * Print "Use" link for this pacakge in the navigation bar.
     */
    protected void navLinkClassUse() {
        navCellStart();
        printHyperLink("package-use.html", "", getText("doclet.navClassUse"),
                       true, "NavBarFont1");
        navCellEnd();
    }

    /**
     * Print "PREV PACKAGE" link in the navigation bar.
     */
    protected void navLinkPrevious() {
        if (prev == null) {
            printText("doclet.Prev_Package");
        } else {
            String path = DirectoryManager.getRelativePath(packagedoc.name(),
                                                           prev.name());
            printHyperLink(path + "package-summary.html", "",
                           getText("doclet.Prev_Package"), true);
        }
    }
                                
    /**
     * Print "NEXT PACKAGE" link in the navigation bar.
     */
    protected void navLinkNext() {
        if (next == null) {
            printText("doclet.Next_Package");
        } else {
            String path = DirectoryManager.getRelativePath(packagedoc.name(),
                                                           next.name());
            printHyperLink(path + "package-summary.html", "",
                           getText("doclet.Next_Package"), true);
        }
    }

    /**
     * Print "Tree" link in the navigation bar. This will be link to the package
     * tree file.
     */
    protected void navLinkTree() {
        navCellStart();
        printHyperLink("package-tree.html", "", getText("doclet.Tree"),
                       true, "NavBarFont1");
        navCellEnd();
    }
}



