/*
 * @(#)SerializedFormWriter.java	1.9 00/02/02
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
 * Generate the Serialized Form Information Page.
 *
 * @author Atul M Dambalkar
 */
public class SerializedFormWriter extends SubWriterHolderWriter {

    public SerializedFormWriter(String filename)
                         throws IOException, DocletAbortException {
        super(filename);
    }

    /**
     * Generate a serialized form page.
     */
    public static void generate(RootDoc root) throws DocletAbortException {
            SerializedFormWriter serialgen;
            String filename = "serialized-form.html";
            try {
                serialgen = new SerializedFormWriter(filename);
                serialgen.generateSerializedFormFile(root);
                serialgen.close();
            } catch (IOException exc) {
                Standard.configuration().standardmessage.
                    error("doclet.exception_encountered",
                           exc.toString(), filename);
                throw new DocletAbortException();
            }
    }

    /**
     * Generate the serialized form file.
     */
    public void generateSerializedFormFile(RootDoc root) {
        printHeader(getText("doclet.Serialized_Form"));
        navLinks(true);
        hr();

        center();
        h1(); printText("doclet.Serialized_Form"); h1End();
        centerEnd();

        generateContents(root);

        hr();
        navLinks(false);
        printBottom();
        printBodyHtmlEnd();
    }

    /**
     * Generate the serialized form file contents.
     */
    protected void generateContents(RootDoc root) {
        PackageDoc[] packages = Standard.configuration().packages;
        ClassDoc[] cmdlineClasses = root.specifiedClasses();
        boolean first = true;
        for (int i = 0; i < packages.length; i++) {
            ClassDoc[] classes = packages[i].allClasses();
            boolean printPackageName = true;
            Arrays.sort(classes);
            for (int j = 0; j < classes.length; j++) {
                ClassDoc classdoc = classes[j];
                if(classdoc.isClass() && classdoc.isSerializable()) {
                    if (printPackageName) {
                        hr(4, "noshade");
                        printPackageName(packages[i].name());
                        printPackageName = false;
                    }
                    first = false;
                    printSerialMemberInfo(classdoc);
                }
            }
        }
        if (cmdlineClasses.length > 0) {
            Arrays.sort(cmdlineClasses);
            for (int i = 0; i < cmdlineClasses.length; i++) {
                ClassDoc classdoc = cmdlineClasses[i];
                if(classdoc.isClass() && classdoc.isSerializable()) {
                    if (!first) {
                        hr(4, "noshade");
                    }
                    first = false;
                    printSerialMemberInfo(classdoc);
                }
            }
        }
    }

    /**
     * Print all the serializable member information.
     */
    protected void printSerialMemberInfo(ClassDoc cd) {
        String classlink = getQualifiedClassLink(cd);
        anchor(cd.qualifiedName());
        printClassName(getText("doclet.Class_0_implements_serializable", 
                                classlink));

	printSerialMembers(cd);
        p();
    }

    /**
     * Print summary and detail information for the serial members in the
     * class.
     */
    protected void printSerialMembers(ClassDoc cd) {
	new SerialMethodSubWriter(this, cd).printMembers();
	new SerialFieldSubWriter(this, cd).printMembers();
    }

    /**
     * Print the package name in the table format.
     */
    protected void printPackageName(String pkgname) {
        tableHeader();
        tdAlign("center");
        font("+2");
        boldText("doclet.Package");
        print(' ');
        bold(pkgname);
        tableFooter();
    }

    protected void printClassName(String classstr) {
        tableHeader();
        tdColspan(2);
        font("+2");
        bold(classstr);
        tableFooter();
    }

    protected void tableHeader() {
        tableIndexSummary();
        trBgcolorStyle("#CCCCFF", "TableSubHeadingColor");
    }

    protected void tableFooter() {
        fontEnd();
        tdEnd(); trEnd(); tableEnd();
        p(); 
    }
}


