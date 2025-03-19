/*
 * @(#)ClassUseWriter.java	1.9 00/02/17
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
 * Generate class usage information. 
 *
 * @author Robert G. Field
 */
public class ClassUseWriter extends SubWriterHolderWriter {

    final ClassDoc classdoc;
    final Map pkgToSubclass;
    final Map pkgToSubinterface;
    final Map pkgToImplementingClass;
    final Map pkgToField;
    final Map pkgToMethodReturn;
    final Map pkgToMethodArgs;
    final Map pkgToMethodThrows;
    final Map pkgToConstructorArgs;
    final Map pkgToConstructorThrows;
    final SortedSet pkgSet;
    final MethodSubWriter methodSubWriter;
    final ConstructorSubWriter constrSubWriter;
    final FieldSubWriter fieldSubWriter;
    final ClassSubWriter classSubWriter;


    /**
     * Constructor.
     *
     * @param filename the file to be generated. 
     */
    public ClassUseWriter(ClassUseMapper mapper, String path, 
                          String filename, String relpath,
                          ClassDoc classdoc) 
                   throws IOException, DocletAbortException {
        super(path, filename, relpath);
        this.classdoc = classdoc;
        HtmlStandardWriter.currentcd = classdoc;
	this.pkgSet = new TreeSet();
	this.pkgToSubclass = pkgDivide(mapper.classToSubclass);
	this.pkgToSubinterface = pkgDivide(mapper.classToSubinterface);
	this.pkgToImplementingClass = pkgDivide(mapper.classToImplementingClass);
	this.pkgToField = pkgDivide(mapper.classToField);
	this.pkgToMethodReturn = pkgDivide(mapper.classToMethodReturn);
	this.pkgToMethodArgs = pkgDivide(mapper.classToMethodArgs);
	this.pkgToMethodThrows = pkgDivide(mapper.classToMethodThrows);
	this.pkgToConstructorArgs = pkgDivide(mapper.classToConstructorArgs);
	this.pkgToConstructorThrows = pkgDivide(mapper.classToConstructorThrows);
	//tmp test
	if (!pkgSet.equals(mapper.classToPackage.get(classdoc))) {
	    System.err.println("Internal error: package sets don't match: " + pkgSet + " with: " +
			       mapper.classToPackage.get(classdoc));
	}
        methodSubWriter = new MethodSubWriter(this);
        constrSubWriter = new ConstructorSubWriter(this);
        fieldSubWriter = new FieldSubWriter(this);
        classSubWriter = new ClassSubWriter(this);
    }

    private Map pkgDivide(Map classMap) {
        Map map = new HashMap();
        List list= (List)classMap.get(classdoc);
        if (list != null) {
            Iterator it = list.iterator();
            while (it.hasNext()) {
                ProgramElementDoc doc = (ProgramElementDoc)it.next();
                PackageDoc pkg = doc.containingPackage();
                pkgSet.add(pkg);
                List inPkg = (List)map.get(pkg);
                if (inPkg == null) {
                    inPkg = new ArrayList();
                    map.put(pkg, inPkg);
                }
                inPkg.add(doc);
            }
        }
        return map;
    }
	
    /**
     * Generate a class page.
     *
     * @param prev the previous class to generated, or null if no previous.
     * @param classdoc the class to generate.
     * @param next the next class to be generated, or null if no next.
     */
    public static void generate(ClassUseMapper mapper, 
				ClassDoc classdoc) 
                         throws DocletAbortException {
            ClassUseWriter clsgen;
            String path = DirectoryManager.getDirectoryPath(classdoc.
                                                    containingPackage());
            if (path.length() > 0) {
                path += File.separator;
            }
            path += "class-use";
            String filename = classdoc.name() + ".html";
            String pkgname = classdoc.containingPackage().name();
            pkgname += (pkgname.length() > 0)? ".class-use": "class-use";
            String relpath = DirectoryManager.getRelativePath(pkgname); 
            try {
                clsgen = new ClassUseWriter(mapper, path, filename, 
                                            relpath, classdoc);
                clsgen.generateClassUseFile();
                clsgen.close();
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
    protected void generateClassUseFile() throws IOException {

        printClassUseHeader();

	if (pkgSet.size() > 0) {
            generateClassUse();
        } else {
            printText("doclet.ClassUse_No.usage.of.0", 
                     classdoc.qualifiedName());
            p();
        }
        
        printClassUseFooter();
    }        

    protected void generateClassUse() throws IOException {
        if (Standard.configuration().packages.length > 1) {
            generatePackageList();
        }
        generateClassList();
    }

    protected void generatePackageList() throws IOException {
	tableIndexSummary();
	tableHeaderStart("#CCCCFF");
	printText("doclet.ClassUse_Packages.that.use.0",
		  getClassLink(classdoc));
	tableHeaderEnd();

	for (Iterator it = pkgSet.iterator(); it.hasNext();) {
	    PackageDoc pkg = (PackageDoc)it.next();
	    generatePackageUse(pkg);
	}
	tableEnd();
	space();
	p();
    }
        
    protected void generateClassList() throws IOException {
	for (Iterator it = pkgSet.iterator(); it.hasNext();) {
	    PackageDoc pkg = (PackageDoc)it.next();
	    anchor(pkg.name());
	    tableIndexSummary();
	    tableHeaderStart("#CCCCFF");
	    printText("doclet.ClassUse_Uses.of.0.in.1",
		      getClassLink(classdoc), 
		      getPackageLink(pkg));
	    tableHeaderEnd();
	    tableEnd();
            space();
            p();
	    generateClassUse(pkg);
	}
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
     * Print the class use list.
     */ 
    protected void generateClassUse(PackageDoc pkg) throws IOException {
        String classLink = getClassLink(classdoc);
	String pkgLink = getPackageLink(pkg);
        classSubWriter.printUseInfo(pkgToSubclass.get(pkg),
				    getText("doclet.ClassUse_Subclass",
					    classLink, 
					    pkgLink));
        classSubWriter.printUseInfo(pkgToSubinterface.get(pkg),
				    getText("doclet.ClassUse_Subinterface",
					    classLink, 
					    pkgLink));
        classSubWriter.printUseInfo(pkgToImplementingClass.get(pkg),
				    getText("doclet.ClassUse_ImplementingClass",
					    classLink, 
					    pkgLink));
        fieldSubWriter.printUseInfo(pkgToField.get(pkg),
				    getText("doclet.ClassUse_Field",
					    classLink, 
					    pkgLink));
        methodSubWriter.printUseInfo(pkgToMethodReturn.get(pkg),
				    getText("doclet.ClassUse_MethodReturn",
					    classLink, 
					    pkgLink));
        methodSubWriter.printUseInfo(pkgToMethodArgs.get(pkg),
				    getText("doclet.ClassUse_MethodArgs",
					    classLink, 
					    pkgLink));
        methodSubWriter.printUseInfo(pkgToMethodThrows.get(pkg),
				    getText("doclet.ClassUse_MethodThrows",
					    classLink, 
					    pkgLink));
        constrSubWriter.printUseInfo(pkgToConstructorArgs.get(pkg),
				    getText("doclet.ClassUse_ConstructorArgs",
					    classLink, 
					    pkgLink));
        constrSubWriter.printUseInfo(pkgToConstructorThrows.get(pkg),
				    getText("doclet.ClassUse_ConstructorThrows",
					    classLink, 
					    pkgLink));
    }        

    /**
     * Print the header for the class use Listing.
     */
    protected void printClassUseHeader() {
        String cltype = getText(classdoc.isInterface()? 
                                    "doclet.Interface": 
                                    "doclet.Class");
        String clname = classdoc.qualifiedName();
        printHeader(getText("doclet.Window_ClassUse_Header", 
                            Standard.configuration().windowtitle, 
                            cltype, clname));
        navLinks(true);
        hr();
        center();
        h2();
        boldText("doclet.ClassUse_Title", cltype, clname);
        h2End();
        centerEnd();
    }

    /**
     * Print the footer for the class use Listing.
     */
    protected void printClassUseFooter() {
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
        printHyperLink("../package-summary.html", "", 
                       getText("doclet.Package"), true, "NavBarFont1");
        navCellEnd();
    }
                                
    /**
     * Print class page indicator
     */
    protected void navLinkClass() {
        navCellStart();
        printClassLink(classdoc, "", getText("doclet.Class"), true, "NavBarFont1");
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
        if (classdoc.containingPackage().isIncluded()) {
            printHyperLink("../package-tree.html", "", getText("doclet.Tree"),
                           true, "NavBarFont1");
        } else {
            printHyperLink(relativepath + "overview-tree.html", "", 
                           getText("doclet.Tree"), true, "NavBarFont1");
        }
        navCellEnd();
    }

}
