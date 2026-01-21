/*
 * @(#)AbstractIndexWriter.java	1.19 00/02/02
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
 * Generate Index for all the Member Names with Indexing in 
 * Unicode Order. This class is a base class for {@link SingleIndexWriter} and
 * {@link SplitIndexWriter}. It uses the functionality from
 * {@link HtmlStandardWriter} and {@link HtmlWriter} to generate the Index 
 * Contents.
 *
 * @see    IndexBuilder
 * @author Atul M Dambalkar
 */
public class AbstractIndexWriter extends HtmlStandardWriter {

    /**
     * The index of all the members with unicode character.
     */
    protected IndexBuilder indexbuilder;

    /**
     * This constructor will be used by {@link SplitIndexWriter}. Initialises
     * path to this file and relative path from this file.
     * 
     * @param path       Path to the file which is getting generated.
     * @param filename   Name of the file which is getting genrated.
     * @param relpath    Relative path from this file to the current directory.
     * @param indexbuilder Unicode based Index from {@link IndexBuilder}
     */
    protected AbstractIndexWriter(String path, String filename, 
                                  String relpath, IndexBuilder indexbuilder) 
                                  throws IOException {
        super(path, filename, relpath);
        this.indexbuilder = indexbuilder;
    }

    /**
     * This Constructor will be used by {@link SingleIndexWriter}.
     * 
     * @param filename   Name of the file which is getting genrated.
     * @param indexbuilder Unicode based Index form {@link IndexBuilder}
     */
    protected AbstractIndexWriter(String filename, IndexBuilder indexbuilder) 
                                  throws IOException {
        super(filename);
        this.indexbuilder = indexbuilder;
    }

    /**
     * Print the text "Index" in bold format in the navigation bar.
     */
    protected void navLinkIndex() {
        navCellRevStart();
        fontStyle("NavBarFont1Rev");
        boldText("doclet.Index");
        fontEnd();
        navCellEnd();
    }

    /**
     * Generate the member information for the unicode character along with the
     * list of the members.  
     *
     * @param unicode Unicode for which member list information to be generated.
     * @param memberlist List of members for the unicode character.
     */
    protected void generateContents(Character unicode, List memberlist) {
        anchor("_" + unicode + "_");
        h2();
        bold(unicode.toString());
        h2End();
        dl();
        for (int i = 0; i < memberlist.size(); i++) {
            Doc element = (Doc)memberlist.get(i);
            if (element instanceof MemberDoc) {
                printDescription((MemberDoc)element);
            } else if (element instanceof ClassDoc) {
                printDescription((ClassDoc)element);
            } else if (element instanceof PackageDoc) {
                printDescription((PackageDoc)element);
            } 
        }
        dlEnd();
        hr();
    }


    /**
     * Print one line summary comment for the package.
     *
     * @param pd PackageDoc passed.
     */
    protected void printDescription(PackageDoc pd) {
        dt();
        printPackageLink(pd, true); 
        print(" - ");
        print("package " + pd.name());
        dd();
        printSummaryComment(pd); 
    }

    /**
     * Print one line summary comment for the class.
     *
     * @param cd ClassDoc passed.
     */
    protected void printDescription(ClassDoc cd) {
        dt();
        printClassLink(cd, true); 
        print(" - ");
        printClassInfo(cd);
        dd();
        printComment(cd); 
    }

    /**
     * What is the classkind? Print the classkind(class, interface, exception, 
     * error of the class passed. 
     *
     * @param cd ClassDoc.
     */
    protected void printClassInfo(ClassDoc cd) {
        if (cd.isOrdinaryClass()) {
            print("class ");
        } else if (cd.isInterface()) {
            print("interface ");
        } else if (cd.isException()) {
            print("exception ");
        } else {   // error
            print("error ");
        }
        printPreQualifiedClassLink(cd);
        print('.');
    }


    /**
     * Generate Description for Class, Field, Method or Constructor.
     * for Java.* Packages Class Members.
     *
     * @param member MemberDoc for the member of the Class Kind.
     * @see com.sun.javadoc.MemberDoc
     */
    protected void printDescription(MemberDoc element) {
        String name = (element instanceof ExecutableMemberDoc)?
                           element.name() + 
                           ((ExecutableMemberDoc)element).flatSignature():
                           element.name();
        ClassDoc containing = element.containingClass();
        String qualname = containing.qualifiedName();
        String baseClassName = containing.name();
        dt();
        printDocLink(element, name, true);
        println(" - ");
        printMemberDesc(element);
        println();
        dd();
        printComment(element); 
        println();
    }


    /**
     * Print comment for each element in the index. If the element is deprecated
     * and it has a @deprecated tag, use that comment. Else if the containing
     * class for this element is deprecated, then add the word "Deprecated." at
     * the start and then print the normal comment.
     *
     * @param element Index element.
     */
    protected void printComment(ProgramElementDoc element) {
        Tag[] tags;
        if ((tags = element.tags("deprecated")).length > 0) {
            boldText("doclet.Deprecated"); space();
            printInlineDeprecatedComment(tags[0]);
        } else {
            ClassDoc cont = element.containingClass();
            while (cont != null) {
                if (cont.tags("deprecated").length > 0) {
                    boldText("doclet.Deprecated"); space();
                    break;
                }
                cont = cont.containingClass();
            }
            printSummaryComment(element);
        }
    }

    /**
     * Print description about the Static Varible/Method/Constructor for a
     * member.
     * 
     * @param member MemberDoc for the member within the Class Kind.
     * @see com.sun.javadoc.MemberDoc
     */
    protected void printMemberDesc(MemberDoc member) {
        ClassDoc containing = member.containingClass();
        String classdesc = (containing.isInterface()? "interface ": "class ") + 
                           getPreQualifiedClassLink(containing);
        if (member.isField()) {
            if (member.isStatic()) {
                printText("doclet.Static_variable_in", classdesc);
            } else {
                printText("doclet.Variable_in", classdesc);
            }
        } else if (member.isConstructor()) {
            printText("doclet.Constructor_for", classdesc);
        } else if (member.isMethod()) {
            if (member.isStatic()) {
                printText("doclet.Static_method_in", classdesc);
            } else {
                printText("doclet.Method_in", classdesc);
            }
        }               
    }
}
