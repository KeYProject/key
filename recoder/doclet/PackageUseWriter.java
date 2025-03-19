/*
 * @(#)PackageUseWriter.java	1.6 00/02/02
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
import java.util.*;

/**
 * Generate package usage information. 
 *
 * @author Robert G. Field
 */
public class PackageUseWriter extends SubWriterHolderWriter {

    final PackageDoc pkgdoc;
    final SortedMap usingPackageToUsedClasses = new TreeMap();  

    /**
     * Constructor.
     *
     * @param filename the file to be generated. 
     */
    public PackageUseWriter(ClassUseMapper mapper, String filename, 
            PackageDoc pkgdoc) throws IOException, DocletAbortException {
        super(DirectoryManager.getDirectoryPath(pkgdoc), 
              filename, 
              DirectoryManager.getRelativePath(pkgdoc.name()));
        this.pkgdoc = pkgdoc;

        // by examining all classes in this package, find what packages
        // use these classes - produce a map between using package and
        // used classes.
        ClassDoc[] content = pkgdoc.allClasses();
        for (int i = 0; i < content.length; ++i) {
            ClassDoc usedClass = content[i];
            Set usingClasses = (Set)mapper.classToClass.get(usedClass);
            if (usingClasses != null) {
                for (Iterator it = usingClasses.iterator(); it.hasNext(); ) {
                    ClassDoc usingClass = (ClassDoc)it.next();
                    PackageDoc usingPackage = usingClass.containingPackage();
                    Set usedClasses = (Set)usingPackageToUsedClasses
                                                     .get(usingPackage);
                    if (usedClasses == null) {
                        usedClasses = new TreeSet();
                        usingPackageToUsedClasses.put(usingPackage, 
                                                      usedClasses);
                    }
                    usedClasses.add(usedClass);
                }
            }
        }
    }

    /**
     * Generate a class page.
     *
     * @param prev the previous class to generated, or null if no previous.
     * @param classdoc the class to generate.
     * @param next the next class to be generated, or null if no next.
     */
    public static void generate(ClassUseMapper mapper, 
				PackageDoc pkgdoc) throws DocletAbortException {
            PackageUseWriter pkgusegen;
            String filename = "package-use.html";
            try {
                pkgusegen = new PackageUseWriter(mapper, filename, pkgdoc);
                pkgusegen.generatePackageUseFile();
                pkgusegen.close();
            } catch (IOException exc) {
                Standard.configuration().standardmessage.
                    error("doclet.exception_encountered",
                           exc.toString(), filename);
                throw new DocletAbortException();
            }
    }


    /** 
     * Print the class use list.
     */ 
    protected void generatePackageUseFile() throws IOException {
        printPackageUseHeader();

	if (usingPackageToUsedClasses.isEmpty()) {
            printText("doclet.ClassUse_No.usage.of.0", pkgdoc.name());
            p();
        } else {
            generatePackageUse();
        }
        
        printPackageUseFooter();
    }        

    /** 
     * Print the class use list.
     */ 
    protected void generatePackageUse() throws IOException {
        if (Standard.configuration().packages.length > 1) {
            generatePackageList();
        }
        generateClassList();
    }

    protected void generatePackageList() throws IOException {
	tableIndexSummary();
	tableHeaderStart("#CCCCFF");
	printText("doclet.ClassUse_Packages.that.use.0",
		  getPackageLink(pkgdoc));
	tableHeaderEnd();

	Iterator it = usingPackageToUsedClasses.keySet().iterator();
        while (it.hasNext()) {
	    PackageDoc pkg = (PackageDoc)it.next();
	    generatePackageUse(pkg);
	}
	tableEnd();
	space();
	p();
    }
        
    protected void generateClassList() throws IOException {
	Iterator itp = usingPackageToUsedClasses.keySet().iterator();
        while (itp.hasNext()) {
	    PackageDoc usingPackage = (PackageDoc)itp.next();
	    anchor(usingPackage.name());
	    tableIndexSummary();
	    tableHeaderStart("#CCCCFF");
	    printText("doclet.ClassUse_Classes.in.0.used.by.1",
		      getPackageLink(pkgdoc),
                      getPackageLink(usingPackage));
            Iterator itc = 
                  ((Collection)usingPackageToUsedClasses.get(usingPackage))
                       .iterator();
            while (itc.hasNext()) {
                printClassRow((ClassDoc)itc.next(), usingPackage);
            }
	    tableHeaderEnd();
	    tableEnd();
            space();
            p();
	}
    }        

    protected void printClassRow(ClassDoc usedClass, PackageDoc usingPackage) {
        String path = pathString(usedClass, 
                                 "class-use/" + usedClass.name() + ".html");

        trBgcolorStyle("white", "TableRowColor");
        summaryRow(0);
        bold();
        printHyperLink(path, usingPackage.name(), usedClass.name(), true);
        boldEnd();
        println(); br();
        printNbsps();
        printIndexComment(usedClass); 
        summaryRowEnd();
        trEnd(); 
    }

    /** 
     * Print the package use list.
     */ 
    protected void generatePackageUse(PackageDoc pkg) throws IOException {
        trBgcolorStyle("white", "TableRowColor");
	summaryRow(0);
	printHyperLink("", pkg.name(), pkg.name(), true);
	summaryRowEnd();
	summaryRow(0);
	printSummaryComment(pkg);
	space();
	summaryRowEnd();
	trEnd();
    }

    /**
     * Print the header for the class use Listing.
     */
    protected void printPackageUseHeader() {
        String packageLabel = getText("doclet.Package");
        String name = pkgdoc.name();
        printHeader(getText("doclet.Window_ClassUse_Header", 
                            Standard.configuration().windowtitle, 
                            packageLabel, name));
        navLinks(true);
        hr();
        center();
        h2();
        boldText("doclet.ClassUse_Title", packageLabel, name);
        h2End();
        centerEnd();
    }

    /**
     * Print the footer for the class use Listing.
     */
    protected void printPackageUseFooter() {
        hr();
        navLinks(false);
        printBottom();
        printBodyHtmlEnd();
    }


    /**
     * Print this package link
     */
    protected void navLinkPackage() {
        navCellStart();
        printHyperLink("package-summary.html", "", getText("doclet.Package"),
                        true, "NavBarFont1");
        navCellEnd();
    }
                                
    /**
     * Print class use link
     */
    protected void navLinkClassUse() {
        navCellRevStart();
        fontStyle("NavBarFont1Rev");
        boldText("doclet.navClassUse");
        fontEnd();
        navCellEnd();
    }

    protected void navLinkTree() {
        navCellStart();
        printHyperLink("package-tree.html", "", getText("doclet.Tree"),
                        true, "NavBarFont1");
        navCellEnd();
    }

}
