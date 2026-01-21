/*
 * @(#)AbstractSubWriter.java	1.29 00/02/17
 *
 * Copyright 1997-2000 Sun Microsystems, Inc. All Rights Reserved.
 * 
 * This software is the proprietary information of Sun Microsystems, Inc.  
 * Use is subject to license terms.
 * 
 */



import com.sun.tools.doclets.*;
import com.sun.javadoc.*;
import java.util.*;
import java.lang.reflect.Modifier;

/**
 *
 * @author Robert Field
 * @author Atul M Dambalkar
 */
public abstract class AbstractSubWriter {

    protected final SubWriterHolderWriter writer;
    protected final ClassDoc classdoc;

    public VisibleMemberMap visibleMemberMap = null;
    public List visibleClasses = null;
    public boolean nodepr = Standard.configuration().nodeprecated;

    public AbstractSubWriter(SubWriterHolderWriter writer, ClassDoc classdoc) {
        this.writer = writer;
        this.classdoc = classdoc;
        buildVisibleMemberMap();
    }

    public AbstractSubWriter(SubWriterHolderWriter writer) {
        this.writer = writer;
        classdoc = null;
    }

    /*** abstracts ***/

    public abstract int getMemberKind();

    public abstract void printSummaryLabel(ClassDoc cd);

    public abstract void printInheritedSummaryLabel(ClassDoc cd);

    public abstract void printSummaryAnchor(ClassDoc cd);

    public abstract void printInheritedSummaryAnchor(ClassDoc cd);

    protected abstract void printSummaryType(ProgramElementDoc member);

    protected abstract void printSummaryLink(ClassDoc cd, 
                                             ProgramElementDoc member);

    protected abstract void printInheritedSummaryLink(ClassDoc cd, 
                                                     ProgramElementDoc member);

    protected abstract void printHeader(ClassDoc cd);

    protected abstract void printBodyHtmlEnd(ClassDoc cd);

    protected abstract void printMember(ProgramElementDoc elem);

    protected abstract void printDeprecatedLink(ProgramElementDoc member);

    protected abstract void printNavSummaryLink(ClassDoc cd, boolean link);

    protected abstract void printNavDetailLink(boolean link);

    /***  ***/

    protected void print(String str) {
        writer.print(str);
        writer.displayLength += str.length();
    }

    protected void print(char ch) {
        writer.print(ch);
        writer.displayLength++;
    }

    protected void bold(String str) {
        writer.bold(str);
        writer.displayLength += str.length();
    }

    protected void printTypeLinkNoDimension(Type type) {
        ClassDoc cd = type.asClassDoc();
	if (cd == null) {
	    print(type.typeName()); 
	} else {
	    writer.printClassLink(cd);
	}
    }

    protected void printTypeLink(Type type) {
        printTypeLinkNoDimension(type);
        print(type.dimension());
    }

    /**
     * Return a string describing the access modifier flags.
     * Don't include native or synchronized.
     *
     * The modifier names are returned in canonical order, as
     * specified by <em>The Java Language Specification</em>.
     */
    protected String modifierString(MemberDoc member) {
        int ms = member.modifierSpecifier();
        int no = Modifier.NATIVE | Modifier.SYNCHRONIZED;
	return Modifier.toString(ms & ~no);
    }

    protected String typeString(MemberDoc member) {
        String type = "";
        if (member instanceof MethodDoc) {
            type = ((MethodDoc)member).returnType().toString();
        } else if (member instanceof FieldDoc) {
            type = ((FieldDoc)member).type().toString();
        }
        return type;
    }
 
    protected void printModifiers(MemberDoc member) {
        String mod;
        mod = modifierString(member);
        if(mod.length() > 0) {
            print(mod);
            print(' ');
        }
    }

    protected void printTypedName(Type type, String name) {
        if (type != null) {
            printTypeLink(type);
        }
        if(name.length() > 0) {
            writer.space();
            writer.print(name);
        }
    }

    protected String makeSpace(int len) {
        if (len <= 0) {
            return "";
        }
        StringBuffer sb = new StringBuffer(len);
        for(int i = 0; i < len; i++) {
            sb.append(' ');
	}
        return sb.toString();
    }

    /**
     * Print 'static' if static and type link.
     */ 
    protected void printStaticAndType(boolean isStatic, Type type) {
        writer.printTypeSummaryHeader();
        if (isStatic) {
            print("static"); 
        }
        writer.space();
        if (type != null) {
            printTypeLink(type); 
        }
        writer.printTypeSummaryFooter();
    }

    protected void printModifierAndType(ProgramElementDoc member, Type type) {
        writer.printTypeSummaryHeader();
        printModifier(member);
        if (type == null) {
	    if (member.isClass()) {
                print("class");
            } else {
	        print("interface");
            }
        } else {
            printTypeLink(type); 
        }
        writer.printTypeSummaryFooter();
    }

    protected void printModifier(ProgramElementDoc member) {
        if (member.isProtected()) {
            print("protected ");
        } else if (member.isPrivate()) {
            print("private ");
        } else if (!member.isPublic()) { // Package private
            writer.printText("doclet.Package_private");
            print(" ");
        }
        if (member.isMethod() && ((MethodDoc)member).isAbstract()) {
            print("abstract ");
        }
        if (member.isStatic()) {
            print("static");
        }
        writer.space();
    }

    protected void printComment(ProgramElementDoc member) {
        if (member.inlineTags().length > 0) {
            writer.dd();
            writer.printInlineComment(member);
        }
    }

    protected void printTags(ProgramElementDoc member) {
        Tag[] since = member.tags("since");
        if (member.seeTags().length + since.length > 0) {
            writer.dd();
            writer.dl();
            writer.printSeeTags(member);
            writer.printSinceTag(member);
            writer.dlEnd();
            writer.ddEnd();
        }
    }

    protected String name(ProgramElementDoc member) {
        return member.name();
    }

    protected void printDeprecated(ProgramElementDoc member) {
        Tag[] deprs = member.tags("deprecated");
        if (deprs.length > 0) {
	    writer.dd();
            writer.boldText("doclet.Deprecated");
            writer.space();
            writer.printInlineDeprecatedComment(deprs[0]);
            writer.p();
        } else {
            printDeprecatedClassComment(member);
        }
    }

    protected void printDeprecatedClassComment(ProgramElementDoc member) {
        Tag[] deprs = member.containingClass().tags("deprecated");
        if (deprs.length > 0) {
            writer.dd();
            writer.boldText("doclet.Deprecated");
            writer.space();
        }
    }  
  
    protected void printHead(MemberDoc member) {
        writer.h3();
        writer.print(member.name());
        writer.h3End();
    }

    protected void printFullComment(ProgramElementDoc member) {
        writer.dl();
        printDeprecated(member);
        printCommentAndTags(member);
        writer.dlEnd();
    }

    protected void printCommentAndTags(ProgramElementDoc member) {
        printComment(member);
        printTags(member);
    }

    /**
     * Forward to containing writer
     */
    public void printSummaryHeader(ClassDoc cd) {
        writer.printSummaryHeader(this, cd);
    }

    /**
     * Forward to containing writer
     */
    public void printInheritedSummaryHeader(ClassDoc cd) {
        writer.printInheritedSummaryHeader(this, cd);
    }

    /**
     * Forward to containing writer
     */
    public void printInheritedSummaryFooter(ClassDoc cd) {
        writer.printInheritedSummaryFooter(this, cd);
    }

    /**
     * Forward to containing writer
     */
    public void printSummaryFooter(ClassDoc cd) {
        writer.printSummaryFooter(this, cd);
    }

    /**
     * Forward to containing writer
     */
    public void printSummaryMember(ClassDoc cd, ProgramElementDoc member) {
        writer.printSummaryMember(this, cd, member);
    }

    /**
     * Forward to containing writer
     */
    public void printInheritedSummaryMember(ClassDoc cd, 
                                            ProgramElementDoc member) {
        writer.printInheritedSummaryMember(this, cd, member);
    }

    public void printMembersSummary() {
        List members = new ArrayList(members(classdoc));
        if (members.size() > 0) {
            printSummaryHeader(classdoc);
            Collections.sort(members);
            for (int i = 0; i < members.size(); ++i) {
                printSummaryMember(classdoc, 
                                   (ProgramElementDoc)(members.get(i)));
            }   
            printSummaryFooter(classdoc);
        }
    }

    public void printInheritedMembersSummary() {
        for (int i = 0; i < visibleClasses.size(); i++) {
            ClassDoc inhclass = (ClassDoc)(visibleClasses.get(i));
            if (inhclass == classdoc) {
                continue;
            }
            List inhmembers = new ArrayList(members(inhclass));
            if (inhmembers.size() > 0) {
                Collections.sort(inhmembers);
                printInheritedSummaryHeader(inhclass);
                printInheritedSummaryMember(inhclass, 
                                  (ProgramElementDoc)(inhmembers.get(0)));
                for (int j = 1; j < inhmembers.size(); ++j) {
                    print(", "); 
                    printInheritedSummaryMember(inhclass, 
                                    (ProgramElementDoc)(inhmembers.get(j)));
                }
                printInheritedSummaryFooter(inhclass);
            }
        }
    }
 
    public void printMembers() {
        List members = members(classdoc);
        if (members.size() > 0) {
            printHeader(classdoc);
            for (int i = 0; i < members.size(); ++i) {
                if (i > 0) {
                    writer.printMemberHeader();
                }
                writer.println("");
                printMember((ProgramElementDoc)(members.get(i)));
                writer.printMemberFooter();
            }
            printBodyHtmlEnd(classdoc);
        }
    }

    /**
     * Generate the code for listing the deprecated APIs. Create the table
     * format for listing the API. Call methods from the sub-class to complete
     * the generation.
     */
    protected void printDeprecatedAPI(List deprmembers, String headingKey) {
        if (deprmembers.size() > 0) {
            writer.tableIndexSummary();
            writer.tableHeaderStart("#CCCCFF");
            writer.boldText(headingKey);
            writer.tableHeaderEnd();
            for (int i = 0; i < deprmembers.size(); i++) {
                ProgramElementDoc member =(ProgramElementDoc)deprmembers.get(i);
                ClassDoc cd = member.containingClass();
                writer.trBgcolorStyle("white", "TableRowColor");
                writer.summaryRow(0);
                printDeprecatedLink(member);
                writer.br();
                writer.printNbsps();
                writer.printInlineDeprecatedComment(member.tags("deprecated")[0]);
                writer.space();
                writer.summaryRowEnd();
                writer.trEnd();
            }
            writer.tableEnd();
            writer.space();
            writer.p();
        }
    }

    /**
     * Print use info.
     */
    protected void printUseInfo(Object mems, String heading) {
        if (mems == null) {
            return;
        }
        List members = (List)mems;
        if (members.size() > 0) {
            writer.tableIndexSummary();
            writer.tableUseInfoHeaderStart("#CCCCFF");
            writer.print(heading);
            writer.tableHeaderEnd();
            for (Iterator it = members.iterator(); it.hasNext(); ) {
                ProgramElementDoc pgmdoc = (ProgramElementDoc)it.next();
                ClassDoc cd = pgmdoc.containingClass();

                writer.printSummaryLinkType(this, pgmdoc);
                if (cd != null && !(pgmdoc instanceof ConstructorDoc) 
                               && !(pgmdoc instanceof ClassDoc)) {
                    // Add class context
                    writer.bold(cd.name() + ".");
                }
                printSummaryLink(cd, pgmdoc);
                writer.printSummaryLinkComment(this, pgmdoc);     
            }
            writer.tableEnd();
            writer.space();
            writer.p();
        }
    }

    protected void navSummaryLink() {
        List members = members(classdoc);
        if (members.size() > 0) {
            printNavSummaryLink(null, true);
            return;
        } else {
            ClassDoc icd = classdoc.superclass();
            while (icd != null) {
                List inhmembers = members(icd);
                if (inhmembers.size() > 0) {
                    printNavSummaryLink(icd, true);
                    return;
                }
                icd = icd.superclass();
            }
        }
        printNavSummaryLink(null, false);
    }
   
    protected void navDetailLink() {
        List members = visibleMemberMap.getMembersFor(classdoc);
        printNavDetailLink(members.size() > 0? true: false);
    }           

    protected void serialWarning(String key, String a1, String a2) {
        if (Standard.configuration().serialwarn) {
            Standard.configuration().standardmessage.warning(key, a1, a2);
        }
    }

    public void buildVisibleMemberMap() {
        visibleMemberMap = new VisibleMemberMap(classdoc, getMemberKind(), 
                                                nodepr);
        visibleClasses = visibleMemberMap.getVisibleClassesList();       
    }

    public ProgramElementDoc[] eligibleMembers(ProgramElementDoc[] members) {
        return nodepr? Util.excludeDeprecatedMembers(members): members;
    }

    public List members(ClassDoc cd) {
        return visibleMemberMap.getMembersFor(cd);
    }
}  
    
    
