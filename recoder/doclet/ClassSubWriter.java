/*
 * @(#)ClassSubWriter.java	1.19 00/02/02
 *
 * Copyright 1997-2000 Sun Microsystems, Inc. All Rights Reserved.
 * 
 * This software is the proprietary information of Sun Microsystems, Inc.  
 * Use is subject to license terms.
 * 
 */



import com.sun.tools.doclets.*;
import com.sun.javadoc.*;

/**
 *
 * @author Robert Field
 * @author Atul M Dambalkar
 */
public class ClassSubWriter extends AbstractSubWriter {

    public ClassSubWriter(SubWriterHolderWriter writer, ClassDoc classdoc) {
        super(writer, classdoc);
    }

    public ClassSubWriter(SubWriterHolderWriter writer) {
        super(writer);
    }

    public int getMemberKind() {
        return VisibleMemberMap.INNERCLASSES;
    }

    public void printSummaryLabel(ClassDoc cd) {
        writer.boldText("doclet.Inner_Class_Summary"); 
    }

    public void printSummaryAnchor(ClassDoc cd) {
        writer.anchor("inner_class_summary"); 
    }
    
    public void printInheritedSummaryAnchor(ClassDoc cd) {
        writer.anchor("inner_classes_inherited_from_class_" + 
                       cd.qualifiedName());
    }   
    
    public void printInheritedSummaryLabel(ClassDoc cd) {
        String clslink = writer.getPreQualifiedClassLink(cd);
        writer.bold();
        writer.printText("doclet.Inner_Classes_Inherited_From_Class", clslink);
        writer.boldEnd();
    }

    protected void printSummaryLink(ClassDoc cd, ProgramElementDoc member) {
        writer.bold();
        writer.printClassLink((ClassDoc)member);
        writer.boldEnd();
    }

    protected void printInheritedSummaryLink(ClassDoc cd, 
                                             ProgramElementDoc member) {
        writer.printClassLink((ClassDoc)member);
    }
  
    protected void printSummaryType(ProgramElementDoc member) {
        ClassDoc cd = (ClassDoc)member;
        printModifierAndType(cd, null);
    }

    protected void printHeader(ClassDoc cd) {
        // N.A.
    }

    protected void printBodyHtmlEnd(ClassDoc cd) {
        // N.A.
    }

    protected void printMember(ProgramElementDoc member) {
        // N.A.
    }

    protected void printDeprecatedLink(ProgramElementDoc member) {
        writer.printQualifiedClassLink((ClassDoc)member);
    }

    protected void printNavSummaryLink(ClassDoc cd, boolean link) {
        if (link) {
            writer.printHyperLink("", (cd == null)? 
                                        "inner_class_summary":
                                        "inner_classes_inherited_from_class_" +
                                          cd.qualifiedName(),
                                  writer.getText("doclet.navInner"));
        } else {               
            writer.printText("doclet.navInner");
        } 
    }

    protected void printNavDetailLink(boolean link) {
    }

    protected void printMemberLink(ProgramElementDoc member) {
    }

    protected void printMembersSummaryLink(ClassDoc cd, ClassDoc icd, 
                                           boolean link) {
        if (link) {
            writer.printHyperLink(cd.name() + ".html",
                                  (cd == icd)? 
                                       "inner_class_summary":
                                       "inner_classes_inherited_from_class_" +
                                        icd.qualifiedName(),
                                 writer.getText("doclet.Inner_Class_Summary"));
        } else {               
            writer.printText("doclet.Inner_Class_Summary");
        } 
    }
}  
    
    
