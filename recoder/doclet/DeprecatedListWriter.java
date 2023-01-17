/*
 * @(#)DeprecatedListWriter.java	1.20 00/02/02
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
 * Generate File to list all the deprecated classes and class members with the
 * appropriate links. 
 *
 * @see java.util.List
 * @author Atul M Dambalkar
 */
public class DeprecatedListWriter extends SubWriterHolderWriter {

    /**
     * Constructor.
     *
     * @param filename the file to be generated. 
     */
    public DeprecatedListWriter(String filename) throws IOException {
        super(filename);
    }

    /** 
     * Get list of all the deprecated classes and members in all the Packages 
     * specified on the Command Line. 
     * Then instantiate DeprecatedListWriter and generate File.
     *
     * @param root Root of the Document
     */ 
    public static void generate(RootDoc root) throws DocletAbortException {
        String filename = "deprecated-list.html";
        try {
            DeprecatedListWriter depr = new DeprecatedListWriter(filename);
            depr.generateDeprecatedListFile(new DeprecatedAPIListBuilder(root));
            depr.close();
        } catch (IOException exc) {
 Standard.configuration().standardmessage.error("doclet.exception_encountered",
                                                 exc.toString(), filename);
            throw new DocletAbortException();
        }
    }

    /** 
     * Print the deprecated API list. Separately print all class kinds and 
     * member kinds.
     *
     * @param deprapi list of deprecated API built already.
     */ 
    protected void generateDeprecatedListFile(DeprecatedAPIListBuilder deprapi)
                                                        throws IOException {
        ClassSubWriter classW = new ClassSubWriter(this);
        FieldSubWriter fieldW = new FieldSubWriter(this);
        MethodSubWriter methodW = new MethodSubWriter(this);
        ConstructorSubWriter consW = new ConstructorSubWriter(this);
        printDeprecatedHeader();

        classW.printDeprecatedAPI(deprapi.getDeprecatedClasses(),
                                  "doclet.Deprecated_Classes");
        classW.printDeprecatedAPI(deprapi.getDeprecatedInterfaces(),
                                  "doclet.Deprecated_Interfaces");
        classW.printDeprecatedAPI(deprapi.getDeprecatedExceptions(),
                                  "doclet.Deprecated_Exceptions");
        classW.printDeprecatedAPI(deprapi.getDeprecatedErrors(),
                                  "doclet.Deprecated_Errors");
        fieldW.printDeprecatedAPI(deprapi.getDeprecatedFields(),
                                  "doclet.Deprecated_Fields");
        methodW.printDeprecatedAPI(deprapi.getDeprecatedMethods(), 
                                   "doclet.Deprecated_Methods");
        consW.printDeprecatedAPI(deprapi.getDeprecatedConstructors(), 
                                 "doclet.Deprecated_Constructors");
        
        printDeprecatedFooter();
    }        

    /**
     * Print the navigation bar and header for the deprecated API Listing.
     */
    protected void printDeprecatedHeader() {
        printHeader(getText("doclet.Window_Deprecated_List",
                             Standard.configuration().windowtitle));
        navLinks(true);
        hr();
        center();
        h2();
        boldText("doclet.Deprecated_API");
        h2End();
        centerEnd();
    }

    /**
     * Print the navigation bar and the footer for the deprecated API Listing.
     */
    protected void printDeprecatedFooter() {
        hr();
        navLinks(false);
        printBottom();
        printBodyHtmlEnd();
    }

    /**
     * Highlight the word "Deprecated" in the navigation bar as this is the same
     * page.
     */
    protected void navLinkDeprecated() {
        navCellRevStart();
        fontStyle("NavBarFont1Rev");
        boldText("doclet.navDeprecated");
        fontEnd();
        navCellEnd();
    }
}
