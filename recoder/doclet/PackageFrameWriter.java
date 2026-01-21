/*
 * @(#)PackageFrameWriter.java	1.19 00/02/02
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
 * Class to generate file for each package contents in the left-hand bottom 
 * frame. This will list all the Class Kinds in the package. A click on any
 * class-kind will update the right-hand frame with the clicked class-kind page.
 *
 * @author Atul M Dambalkar
 */
public class PackageFrameWriter extends AbstractPackageWriter {

    /**
     * Constructor to construct PackageFrameWriter object and to generate 
     * "package-frame.html" file in the respective package directory. 
     * For example for package "java.lang" this will generate file 
     * "package-frame.html" file in the "java/lang" directory. It will also 
     * create "java/lang" directory in the current or the destination directory
     * if it doesen't exist.
     *
     * @param path Directories in this path will be created if they are not 
     * already there.
     * @param filename Name of the package summary file to be generated, 
     * "package-frame.html".
     * @param packagedoc PackageDoc under consideration.
     */
    public PackageFrameWriter(String path, String filename, 
                              PackageDoc packagedoc) 
                              throws IOException, DocletAbortException {
        super(path, filename, packagedoc);
    }

    /**
     * Generate a package summary page for the left-hand bottom frame. Construct
     * the PackageFrameWriter object and then uses it generate the file.
     *
     * @param pkg The package for which "pacakge-frame.html" is to be generated.
     */
    public static void generate(PackageDoc pkg) throws DocletAbortException {
        PackageFrameWriter packgen;
        String path = DirectoryManager.getDirectoryPath(pkg);
        String filename = "package-frame" + ".html";
        try {
            packgen = new PackageFrameWriter(path, filename, pkg);
            packgen.generatePackageFile();
            packgen.close();
        } catch (IOException exc) {
            Standard.configuration().standardmessage.
                    error("doclet.exception_encountered", 
                           exc.toString(), filename);
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
                                 getText("doclet.Interfaces"));
        generateClassKindListing(packagedoc.ordinaryClasses(),
                                 getText("doclet.Classes"));
        generateClassKindListing(packagedoc.exceptions(),
                                 getText("doclet.Exceptions"));
        generateClassKindListing(packagedoc.errors(),
                                 getText("doclet.Errors"));
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
            printPackageTableHeader();
            fontSizeStyle("+1", "FrameHeadingFont");
            print(label);
            fontEnd();
            println("&nbsp;");
            fontStyle("FrameItemFont");
            for (int i = 0; i < arr.length; i++) {
                if (!Util.isCoreClass(arr[i]) || !isGeneratedDoc(arr[i])) {
                    continue;
                }
                br();
                printTargetClassLink(arr[i], "classFrame");
            }
            fontEnd();
            printPackageTableFooter();
            println();
        }
    }

    /**
     * Print the package link at the top of the class kind listing. Clicking 
     * this link, package-summary page will appear in the right hand frame.
     *
     * @param heading Top Heading to be used for the class kind listing.
     */
    protected void printPackageHeader(String heading) {
        fontSizeStyle("+1", "FrameTitleFont");
        printTargetPackageLink(packagedoc, "classFrame", heading);
        fontEnd();
    }
   
    /**
     * The table for the class kind listing.
     */
    protected void printPackageTableHeader() {
        table();
        tr();
        tdNowrap();
    }
     
    /**
     * Closing Html tags for table of class kind listing.
     */
    protected void printPackageTableFooter() {
        tdEnd();
        trEnd();
        tableEnd();
    }
     
    /**
     * Do nothing. No footer is generated for this page.
     */
    protected void printPackageFooter() {
        
    }
    
    /**
     * Do nothing. Package Description is not generted in this page.
     */
    protected void printPackageDescription() throws IOException {
    }
}



