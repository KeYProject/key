/*
 * @(#)ClassWriter.java	1.45 00/02/02
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
 * Generate the Class Information Page.
 * @see com.sun.javadoc.ClassDoc 
 * @see java.util.Collections
 * @see java.util.List
 * @see java.util.ArrayList
 * @see java.util.HashMap
 *
 * @author Atul M Dambalkar
 * @author Robert Field
 */
public class ClassWriter extends SubWriterHolderWriter {

    protected ClassDoc classdoc;

    protected ClassTree classtree;

    protected ClassDoc prev;

    protected ClassDoc next;

    protected boolean nopackage;

    protected MethodSubWriter methodSubWriter;

    protected ConstructorSubWriter constrSubWriter;

    protected FieldSubWriter fieldSubWriter;

    protected ClassSubWriter innerSubWriter;

    public ClassWriter(String path, String filename, ClassDoc classdoc,
                ClassDoc prev, ClassDoc next, ClassTree classtree,
                boolean nopackage) throws IOException, DocletAbortException {
        super(path, filename, 
         DirectoryManager.getRelativePath(classdoc.containingPackage().name()));
        this.classdoc = classdoc;
        HtmlStandardWriter.currentcd = classdoc;
        this.classtree = classtree;
        this.prev = prev;
        this.next = next;
        this.nopackage = nopackage;
        methodSubWriter = new MethodSubWriter(this, classdoc);
        constrSubWriter = new ConstructorSubWriter(this, classdoc);
        fieldSubWriter = new FieldSubWriter(this, classdoc);
        innerSubWriter = new ClassSubWriter(this, classdoc);
    }

    /**
     * Generate a class page.
     *
     * @param prev the previous class to generated, or null if no previous.
     * @param classdoc the class to generate.
     * @param next the next class to be generated, or null if no next.
     */
    public static void generate(ClassDoc classdoc, ClassDoc prev, 
				ClassDoc next, ClassTree classtree, 
				boolean nopackage) throws DocletAbortException {
            ClassWriter clsgen;
            String path = 
               DirectoryManager.getDirectoryPath(classdoc.containingPackage());
            String filename = classdoc.name() + ".html";
            try {
                clsgen = new ClassWriter(path, filename, classdoc, 
                                         prev, next, classtree, nopackage);
                clsgen.generateClassFile();
                clsgen.close();
            } catch (IOException exc) {
                Standard.configuration().standardmessage.
                    error("doclet.exception_encountered",
                           exc.toString(), filename);
                throw new DocletAbortException();
            }
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
     * Print class page indicator
     */
    protected void navLinkClass() {
        navCellRevStart();
        fontStyle("NavBarFont1Rev");
        boldText("doclet.Class");
        fontEnd();
        navCellEnd();
    }

    /**
     * Print class use link
     */
    protected void navLinkClassUse() {
        navCellStart();
        printHyperLink("class-use/" + filename, "", 
                       getText("doclet.navClassUse"), true, "NavBarFont1");
        navCellEnd();
    }

    /**
     * Print previous package link
     */
    protected void navLinkPrevious() {
        if (prev == null) {
            printText("doclet.Prev_Class"); 
        } else {
            printClassLink(prev, getText("doclet.Prev_Class"), true);
        }
    }
                                
    /**
     * Print next package link
     */
    protected void navLinkNext() {
        if (next == null) {
            printText("doclet.Next_Class"); 
        } else {
            printClassLink(next, getText("doclet.Next_Class"), true);
        }
    }                               

    /**
     * Generate the class file contents.
     */
    public void generateClassFile() {
        String cltype = getText(classdoc.isInterface()? 
                                    "doclet.Interface": 
                                    "doclet.Class") + " ";
        PackageDoc pkg = classdoc.containingPackage();
        String pkgname = (pkg != null)? pkg.name(): "";
        String clname = classdoc.name();
        String label = cltype + ' ' + clname;

        printHeader(getText("doclet.Window_ClassFile_label", 
                            Standard.configuration().windowtitle, label));
        navLinks(true);
        hr();
        println("<!-- ======== START OF CLASS DATA ======== -->");
        h2();
        if (pkgname.length() > 0) {
            font("-1"); print(pkgname); fontEnd(); br();
        }
        print(label);
        h2End();

        // if this is a class (not an interface) then generate 
        // the super class tree.
        if (classdoc.isClass()) {
            pre();
            printTreeForClass(classdoc);
            preEnd();
        }
        
        printSuperImplementedInterfacesInfo();

        printSubClassInterfaceInfo();
        
        if (classdoc.isInterface()) {
            printImplementingClasses();
        }

        printEnclosingClassInfo();

        hr();

        printDeprecated();

        printClassDescription();
        p();
        // generate documentation for the class.
        if (classdoc.inlineTags().length > 0) {
            printInlineComment(classdoc);
            p();
        }
        // Print Information about all the tags here

        if (Standard.configuration().linksources) { //new
           String classname = classdoc.toString(); //new
           classname = classname.replace('.', '/');  //new
           classname = classname.concat(".java");  //new
	   String sourcepath = Standard.configuration().sourcepath; //new
           sourcepath = sourcepath.concat("/" + classname);  //new
	   generateTagInfo(classdoc, sourcepath);  //new
        } else { //new
	   generateTagInfo(classdoc);
	} //new

        hr();
        p();

	printAllMembers();

        println("<!-- ========= END OF CLASS DATA ========= -->");
        hr();
        navLinks(false);
        printBottom();
        printBodyHtmlEnd();
    }

    /**
     * Print summary and detail information for the specified members in the 
     * class.
     */
    protected void printAllMembers() {
        println("<!-- ======== INNER CLASS SUMMARY ======== -->"); println();
	innerSubWriter.printMembersSummary();
	innerSubWriter.printInheritedMembersSummary();
        println(); 
        println("<!-- =========== FIELD SUMMARY =========== -->"); println();
	fieldSubWriter.printMembersSummary();
	fieldSubWriter.printInheritedMembersSummary();
        println(); 
        println("<!-- ======== CONSTRUCTOR SUMMARY ======== -->"); println();
	constrSubWriter.printMembersSummary();
        println(); 
        println("<!-- ========== METHOD SUMMARY =========== -->"); println();
	methodSubWriter.printMembersSummary();
        methodSubWriter.printInheritedMembersSummary();

        p();

        println(); 
        println("<!-- ============ FIELD DETAIL =========== -->"); println();
	fieldSubWriter.printMembers();
        println(); 
        println("<!-- ========= CONSTRUCTOR DETAIL ======== -->"); println();
	constrSubWriter.printMembers();
        println(); 
        println("<!-- ============ METHOD DETAIL ========== -->"); println();
	methodSubWriter.printMembers();
    }


    /**
     * Print the class description regarding iterfaces implemented, classes
     * inheritted.
     */
    protected void printClassDescription() {
        boolean isInterface = classdoc.isInterface();
        dl();
        dt();

        print(classdoc.modifiers() + " ");  

        if (!isInterface) {
            print("class ");
        }
        bold(classdoc.name());

        if (!isInterface) {
            ClassDoc superclass = classdoc.superclass();
            if (superclass != null) {
                dt();
                print("extends ");
                printClassLink(superclass); 
            }
        }

        ClassDoc[] implIntfacs = classdoc.interfaces();
        if (implIntfacs != null && implIntfacs.length > 0) {
            dt();
            print(isInterface? "extends " : "implements ");
            printClassLink(implIntfacs[0]);
            for (int i = 1; i < implIntfacs.length; i++) {
                print(", ");
                printClassLink(implIntfacs[i]);
            }
        }
        dlEnd();
    }
  
    /**
     * Mark the class as deprecated if it is.
     */
    protected void printDeprecated() {
        Tag[] deprs = classdoc.tags("deprecated");
        if (deprs.length > 0) {
            Tag[] commentTags = deprs[0].inlineTags();
            if (commentTags.length > 0) {
                boldText("doclet.Deprecated");
                space();
                printInlineDeprecatedComment(deprs[0]);
            }
            p();
        }
    }

    /**
     * Generate the step like diagram for the class hierarchy.
     */
    protected void printStep(int indent) {
        String spc = spaces(6 * indent - 4);
        print(spc);
        println("|");
        print(spc);
        print("+--");
    }

    /**
     * Print the class hierarchy tree for this class only.
     */
    protected int printTreeForClass(ClassDoc cd) {
        ClassDoc sup = cd.superclass();
        int indent = 0;
        if (sup != null) {
            indent = printTreeForClass(sup);
            printStep(indent);
        }
        if (cd.equals(classdoc)) {
            bold(cd.qualifiedName());
        } else {
            printQualifiedClassLink(cd);
        }
        println();
        return indent + 1;
    }

    /**
     * Which are the sub-classes or sub-interfaces for this class?
     */ 
    protected void printSubClassInterfaceInfo() {
        // Before using TreeBuilder.getSubClassList
        // make sure that tree.html is generated prior.
        if (classdoc.qualifiedName().equals("java.lang.Object") ||
               classdoc.qualifiedName().equals("org.omg.CORBA.Object")) {
            return;    // Don't generate the list, too huge
        }
        List subclasses = classdoc.isClass()? 
                             classtree.subs(classdoc): // it's a class
                             classtree.allSubs(classdoc); // it's an interface
        if (subclasses.size() > 0) {
            printInfoHeader();
            if (classdoc.isClass()) {
                boldText("doclet.Subclasses");
            } else { // this is an interface
                boldText("doclet.Subinterfaces");
            }
            printSubClassLinkInfo(subclasses);
        }
    }

    /**
     * If this is the interface which are the classes, that implement this?
     */
    protected void printImplementingClasses() {
        if (classdoc.qualifiedName().equals("java.lang.Cloneable") || 
                classdoc.qualifiedName().equals("java.io.Serializable")) {
            return;   // Don't generate the list, too big
        }
        List implcl = classtree.implementingclasses(classdoc);
        if (implcl.size() > 0) {
            printInfoHeader();
            boldText("doclet.Implementing_Classes");
            printSubClassLinkInfo(implcl);
        }
    }

    protected void printSuperImplementedInterfacesInfo() {
        ProgramElementDoc[] intarr = Util.getAllInterfaces(classdoc);
        Arrays.sort(intarr);
        if (intarr.length > 0) {
            printInfoHeader();
            boldText(classdoc.isClass()?
		         "doclet.All_Implemented_Interfaces":
                         "doclet.All_Superinterfaces");
            printSubClassLinkInfo(Arrays.asList(intarr));
        }
    }   

    protected void printInfoHeader() {
        dl();
        dt();
    }

    /**
     * Generate a link for the sub-classes.
     */
    protected void printSubClassLinkInfo(List list) {
        int i = 0;
        print(' ');
        dd();
        for (; i < list.size() - 1; i++) {
            printClassLink((ClassDoc)(list.get(i)));
            print(", ");
        }
        printClassLink((ClassDoc)(list.get(i)));
        ddEnd();
        dlEnd();
    }

    protected void navLinkTree() {
        navCellStart();
        if (nopackage) {
            printHyperLink(relativepath + "overview-tree.html", "",
                           getText("doclet.Tree"), true, "NavBarFont1");
        } else {
            printHyperLink("package-tree.html", "", getText("doclet.Tree"),
                           true, "NavBarFont1");
        }
        navCellEnd();
    }

    protected void printSummaryDetailLinks() {
        tr();
        tdVAlignClass("top", "NavBarCell3");
        font("-2");
        print("  ");
        navSummaryLinks();
        fontEnd();
        tdEnd();
        
        tdVAlignClass("top", "NavBarCell3");
        font("-2");
        navDetailLinks();
        fontEnd();
        tdEnd();
        trEnd();
    }   

    protected void navSummaryLinks() {
        printText("doclet.Summary");
        print("&nbsp;");
        innerSubWriter.navSummaryLink();
        navGap();
        fieldSubWriter.navSummaryLink();
        navGap();
        constrSubWriter.navSummaryLink();
        navGap();
        methodSubWriter.navSummaryLink();
    }

    protected void navDetailLinks() {
        printText("doclet.Detail");
        print("&nbsp;");
        fieldSubWriter.navDetailLink();
        navGap();
        constrSubWriter.navDetailLink();
        navGap();
        methodSubWriter.navDetailLink();
    }

    protected void navGap() {
        space();
        print('|');
        space();
    }

    protected void printEnclosingClassInfo() {
        ClassDoc outerClass = classdoc.containingClass(); 
        if (outerClass != null) {
            printInfoHeader();
            boldText("doclet.Enclosing_Class");
            dd();
            printClassLink(outerClass);            
            ddEnd();
            dlEnd();
        }
    }
}


