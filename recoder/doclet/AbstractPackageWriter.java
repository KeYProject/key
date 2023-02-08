/*
 * @(#)AbstractPackageWriter.java	1.14 00/02/02
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
 * Abstract class to generate file for each package contents. Sub-classed to
 * generate specific formats Frame and Non-Frame Output by 
 * {@link PackageIndexFrameWriter} and {@link PackageIndexFrameWriter} 
 * respectively.
 *
 * @author Atul M Dambalkar
 */
public abstract class AbstractPackageWriter extends HtmlStandardWriter {

    /**
     * The package under consideration.
     */
    PackageDoc packagedoc;

    /**
     * Create appropriate directory for the package and also initilise the 
     * relative path from this generated file to the current or
     * the destination directory.
     *
     * @param path Directories in this path will be created if they are not 
     * already there.
     * @param filename Name of the package summary file to be generated.
     * @param packagedoc PackageDoc under consideration.
     */
    public AbstractPackageWriter(String path, String filename, 
                                 PackageDoc packagedoc) 
                                 throws IOException, DocletAbortException {
        super(path, filename,
              DirectoryManager.getRelativePath(packagedoc.name()));
        this.packagedoc = packagedoc;
    }

    protected abstract void generateClassListing();

    protected abstract void printPackageDescription() throws IOException;

    protected abstract void printPackageHeader(String head);

    protected abstract void printPackageFooter();

    /**
     * Generate Individual Package File with Class/Interface/Exceptions and
     * Error Listing with the appropriate links. Calls the methods from the
     * sub-classes to generate the file contents.
     */
    protected void generatePackageFile() throws IOException {
        String pkgName = packagedoc.name();
        String heading = getText("doclet.Window_Package", 
                                  Standard.configuration().windowtitle,
            		          pkgName);
        printHeader(heading);
        printPackageHeader(pkgName);

        generateClassListing();
        printPackageDescription();

        printPackageFooter();
        printBodyHtmlEnd();
    }
   
    /**
     * Highlight "Package" in the navigation bar, as this is the package page.
     */
    protected void navLinkPackage() {
        navCellRevStart();
        fontStyle("NavBarFont1Rev");
        boldText("doclet.Package");
        fontEnd();
        navCellEnd();
    }
}



