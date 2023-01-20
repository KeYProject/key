/*
 * @(#)MethodSubWriter.java	1.27 00/02/02
 *
 * Copyright 1997-2000 Sun Microsystems, Inc. All Rights Reserved.
 * 
 * This software is the proprietary information of Sun Microsystems, Inc.  
 * Use is subject to license terms.
 * 
 */



import java.util.*;
import com.sun.tools.doclets.*;
import com.sun.javadoc.*;

/**
 *
 * @author Robert Field
 * @author Atul M Dambalkar
 */
public class MethodSubWriter extends ExecutableMemberSubWriter {

    public MethodSubWriter(SubWriterHolderWriter writer, ClassDoc classdoc) {
        super(writer, classdoc);
    }

    public MethodSubWriter(SubWriterHolderWriter writer) {
        super(writer);
    }

    public int getMemberKind() { 
        return VisibleMemberMap.METHODS; 
    } 

    public void printSummaryLabel(ClassDoc cd) { 
        writer.boldText("doclet.Method_Summary");  
    } 
 
    public void printSummaryAnchor(ClassDoc cd) {
        writer.anchor("method_summary");
    }

    public void printInheritedSummaryAnchor(ClassDoc cd) {
        writer.anchor("methods_inherited_from_class_" + cd.qualifiedName());
    }   
    
    public void printInheritedSummaryLabel(ClassDoc cd) {
        String classlink = writer.getPreQualifiedClassLink(cd);
        writer.bold();
        writer.printText(cd.isClass()? 
                                "doclet.Methods_Inherited_From_Class":
                                "doclet.Methods_Inherited_From_Interface",
                             classlink);
        writer.boldEnd();
    }

    protected void printSummaryType(ProgramElementDoc member) {
        MethodDoc meth = (MethodDoc)member;
        printModifierAndType(meth, meth.returnType());
    }

    protected void printReturnTag(Tag[] returns) {
        if (returns.length > 0) {
            writer.dt();
            writer.boldText("doclet.Returns");
            writer.dd();
            writer.printInlineComment(returns[0]);
        }
    }

    protected void printOverridden(ClassDoc overridden, MethodDoc method) {
        if (overridden != null) {
            String overriddenclasslink = writer.codeText( 
                                             writer.getClassLink(overridden));
            String methlink = "";
            String name = method.name();
            writer.dt();
            writer.boldText("doclet.Overrides");
            writer.dd();
            methlink = writer.codeText(writer.getClassLink(overridden, 
                                       name + method.signature(), 
                                       name, false));
            writer.printText("doclet.in_class", methlink, overriddenclasslink);
        }
    }

    protected void printTags(ProgramElementDoc member) {
        MethodDoc method = (MethodDoc)member;
        ParamTag[] params = method.paramTags();
        Tag[] returns = method.tags("return");
        Tag[] sinces = method.tags("since");
        ThrowsTag[] thrown = method.throwsTags();
        SeeTag[] sees = method.seeTags();
        ClassDoc[] intfacs = member.containingClass().interfaces();
        ClassDoc overridden = method.overriddenClass();
        if (intfacs.length > 0 || overridden != null) {
            printTagsInfoHeader();
            printImplementsInfo(method);
            printOverridden(overridden, method);
            printTagsInfoFooter();
        }
        if (params.length + returns.length + thrown.length + sinces.length
             + sees.length > 0) {
            printTagsInfoHeader();
            printParamTags(params);
            printReturnTag(returns);
            printThrowsTags(thrown);
            writer.printSinceTag(method);
            writer.printSeeTags(method);
            printTagsInfoFooter();
        } else {   // no tags are specified
            MethodDoc taggedMeth = new TaggedMethodFinder().
                                      search(method.containingClass(), method);
            if (taggedMeth != null) {
                printTagsFromTaggedMethod(taggedMeth);
            }
        }
    }

    /**
     * Print @param, @return, @throws and @see tags only.
     */
    protected void printTagsFromTaggedMethod(MethodDoc method) {
        ParamTag[] params = method.paramTags();
        Tag[] returns = method.tags("return");
        ThrowsTag[] thrown = method.throwsTags();
        SeeTag[] sees = method.seeTags(); 
        ClassDoc cd = method.containingClass();
        String classname = writer.codeText(cd.qualifiedName());
        writer.dd();
        writer.printText(cd.isClass()? 
                            "doclet.Following_From_Class":
                            "doclet.Following_From_Interface",
                        classname);
        writer.ddEnd();
        printTagsInfoHeader();
        printParamTags(params);
        printReturnTag(returns);
        printThrowsTags(thrown);
        writer.printSeeTags(method);
        printTagsInfoFooter();
    }

    protected void printTagsInfoHeader() {
        writer.dd();
        writer.dl();
    }

    protected void printTagsInfoFooter() {
        writer.dlEnd();
        writer.ddEnd();
    }

    protected void printImplementsInfo(MethodDoc method) {
        ClassDoc[] implIntfacs = method.containingClass().interfaces();
        if (implIntfacs.length > 0) {
            MethodDoc implementedMeth = implementedMethod(implIntfacs, method);
            if (implementedMeth != null) {
                ClassDoc intfac = implementedMeth.containingClass();
                String methlink = "";
                String intfaclink = writer.codeText(
                                            writer.getClassLink(intfac));
                writer.dt();
                writer.boldText("doclet.Specified_By");
                writer.dd();
                methlink = writer.codeText(writer.getDocLink(implementedMeth, 
                                                implementedMeth.name())); 
                writer.printText("doclet.in_interface", methlink, intfaclink);
            }
        }
    }
           
    protected MethodDoc implementedMethod(ClassDoc[] intfacs, 
                                          MethodDoc method) {
        for (int i = 0; i < intfacs.length; i++) {
            MethodDoc found = Util.findMethod(intfacs[i], method);
            if (found != null) {
                return found;
            }
            ClassDoc[] iin = intfacs[i].interfaces();
            found = implementedMethod(iin, method);
            if (found != null) {
                return found;
            }
        }
        return null;
    }
                    
    protected void printSignature(ExecutableMemberDoc member) {
        writer.displayLength = 0;
	writer.pre();
	printModifiers(member);
	printReturnType((MethodDoc)member);
	bold(member.name());
	printParameters(member);
	printExceptions(member);
	writer.preEnd();
    }
      
    protected void printComment(ProgramElementDoc member) {
        if (member.inlineTags().length > 0) {
            writer.dd();
            writer.printInlineComment(member);
        } else {
            MethodDoc method = new CommentedMethodFinder().
                                            search(member.containingClass(),
                                                   (MethodDoc)member);
            printCommentFromCommentedMethod(method);  
        }
    }

    protected void printCommentFromCommentedMethod(MethodDoc method) {
        if (method == null) {
            return;
        }
        ClassDoc cd = method.containingClass();
        String classlink = writer.codeText(writer.getClassLink(cd));
        writer.dd();
        writer.boldText(cd.isClass()? 
                            "doclet.Description_From_Class":
                            "doclet.Description_From_Interface",
                        classlink);
        writer.ddEnd();
        writer.dd();
        writer.printInlineComment(method);
    }

    public void printMembersSummary() {
        List members = new ArrayList(members(classdoc));
        if (members.size() > 0) {
	    Collections.sort(members);
            printSummaryHeader(classdoc);
            for (int i = 0; i < members.size(); ++i) {
                MethodDoc member = (MethodDoc)members.get(i);
                boolean commentChanged = false;
                String prevRawComment = "";
                Tag[] tags = member.inlineTags();
                if (tags.length == 0) {
                    prevRawComment = member.getRawCommentText();
                    MethodDoc meth = 
                         new CommentedMethodFinder().search(classdoc, member);
                    if (meth != null) { //set raw comment text for now.
                        member.setRawCommentText(meth.commentText());
                        commentChanged = true;
		    }
                }
                printSummaryMember(classdoc, member);    
                if (commentChanged) {  // reset it to prevRawComment.
		  member.setRawCommentText(prevRawComment);
                }
            }
            printSummaryFooter(classdoc);
        }
    }

    protected void printReturnType(MethodDoc method) {
        Type type = method.returnType();
        if (type != null) {
            printTypeLink(type);
            print(' ');
        }
    }
    
    protected void printHeader(ClassDoc cd) {
        writer.anchor("method_detail");
        writer.printTableHeadingBackground(writer.
                                              getText("doclet.Method_Detail"));
    }

    protected void printNavSummaryLink(ClassDoc cd, boolean link) {
        if (link) {
            writer.printHyperLink("", (cd == null)?
                                          "method_summary":
                                          "methods_inherited_from_class_" +
                                           cd.qualifiedName(),
                                      writer.getText("doclet.navMethod"));
        } else {
            writer.printText("doclet.navMethod");
        }
    }

    protected void printNavDetailLink(boolean link) {
        if (link) {
            writer.printHyperLink("", "method_detail",
                                  writer.getText("doclet.navMethod"));
        } else {
            writer.printText("doclet.navMethod");
        }
    }
}


