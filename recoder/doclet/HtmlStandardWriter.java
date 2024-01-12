/*
 * @(#)HtmlStandardWriter.java	1.37 00/02/02
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
import java.util.*;
import java.lang.*;
import java.text.MessageFormat;


/** 
* Class for the Html Format Code Generation specific to JavaDoc.
* This Class contains methods related to the Html Code Generation which 
* are used extensively while generating the entire documentation.
*
* @since JDK1.2
* @author Atul M Dambalkar
* @author Robert Field
*/
public class HtmlStandardWriter extends HtmlDocWriter {
  
    /**
     * Destination directory name as specified on the command line.
     */
    public static final String destdir = Standard.configuration().destdirname; 

    /**
     * Relative path from the file getting generated to the current or the 
     * destination directory. For example, if the file getting generated is
     * "java/lang/Object.html", then the relative path string is "../..".
     */
    public String relativepath = ""; 

    /**
     * Directory path from the current or the destination directory to the file
     * getting generated. For example, if the file getting generated is 
     * "java/lang/Object.html", then the path string is "java/lang".
     */    
    public String path = "";
 
    /**
     * Name of the file getting generated. If the file getting generated is 
     * "java/lang/Object.html", then the filename is "Object.html".
     */   
    public String filename = "";

    /**
     * Relative path from the destination directory to the current directory.
     * For example if the destination directory is "core/api/docs", then the
     * backpat string will be "../../".
     */
    public String backpath = DirectoryManager.getBackPath(destdir);

    /**
     * The display length used for indentation while generating the class page.
     */
    public int displayLength = 0;

    /** 
     * The classdoc for the class file getting generated.
     */ 
    public static ClassDoc currentcd = null;  // Set this classdoc in the
                                              // ClassWriter.

    /**
     * Constructor to construct the HtmlStandardWriter object.
     *
     * @param filename File to be generated.
     */
    public HtmlStandardWriter(String filename) throws IOException {
        super(filename);
        this.filename = filename;
    }

    /**
     * Constructor to construct the HtmlStandardWriter object.
     *
     * @param path         Value for the variable {@link path}.
     * @param filename     File to be generated.
     * @param relativepath Value for the variable {@link relativepath}.
     */
    public HtmlStandardWriter(String path, String filename, 
                              String relativepath) throws IOException {
        super(path, filename);
        this.path = path;
        this.relativepath = relativepath;
        this.filename = filename;
    }

    public String replaceDocRootDir(String htmlstr) {
	int index = htmlstr.indexOf("{@");
	if (index < 0) {
            return htmlstr;
        }
	String lowHtml = htmlstr.toLowerCase();
        index = lowHtml.indexOf("{@docroot}", index);
        if (index < 0) {
            return htmlstr;
        }
        StringBuffer buf = new StringBuffer();
        int previndex = 0;
        String relpathmod = relativepath.equals("")? ".": relativepath;
        relpathmod = relpathmod.endsWith("/")? 
		      relpathmod.substring(0, relpathmod.length() - 1):
                      relpathmod;
        while (true) {
            index = lowHtml.indexOf("{@docroot}", previndex);
            if (index < 0) {
                buf.append(htmlstr.substring(previndex));
                break;
            }
            buf.append(htmlstr.substring(previndex, index));
            previndex = index + 10;  // length for {@docroot} string
            if (previndex < htmlstr.length() &&
                htmlstr.charAt(previndex) == '/') {  //URL Separator
                buf.append(relpathmod);
            } else {
                buf.append(relativepath);
            }
        } 
        return buf.toString();
    }

    /**
     * Print Html Hyper Link, with target frame.
     *
     * @param link String name of the file.
     * @param where Position in the file
     * @param target Name of the target frame.
     * @param label Tag for the link.
     * @param bold Whether the label should be bold or not?
     */
    public void printTargetHyperLink(String link, String where,
                                     String target, String label,
                                     boolean bold) {
        print(getTargetHyperLink(link, where, target, label, bold));
    }

    /**
     * Get Html Hyper Link, with target frame.
     *
     * @param link String name of the file.
     * @param where Position in the file
     * @param target Name of the target frame.
     * @param label Tag for the link.
     * @param bold Whether the label should be bold or not?
     */
    public String getTargetHyperLink(String link, String where,
                                     String target, String label,
                                     boolean bold) {
        StringBuffer str = new StringBuffer();
        str.append("<A HREF=\"");
        str.append(link);
        if (where.length() > 0) {
            str.append("#" + where);
        }
        str.append("\"");
        str.append(" TARGET=\"");
        str.append(target);
        str.append("\">");
        if(bold) {
            str.append("<B>");
        }
        str.append(label);
        if(bold) {
            str.append("</B>");   
        }
        str.append("</A>");
        return str.toString();
    }

    /**
     * Print Html Hyper Link, with target frame.
     *
     * @param link String name of the file.
     * @param target Name of the target frame.
     * @param label Tag for the link.
     * @param bold Whether the label should be bold or not?
     */
    public void printTargetHyperLink(String link, String target, 
                                     String label, boolean bold) {
       printTargetHyperLink(link, "", target, label, bold);
    }


    /**
     * Print bold Html Hyper Link, with target frame. The label will be bold.
     *
     * @param link String name of the file.
     * @param target Name of the target frame.
     * @param label Tag for the link.
     */
    public void printBoldTargetHyperLink(String link, String target, 
                                         String label) {
        printTargetHyperLink(link, target, label, true);
    }

    /**
     * Print Html Hyper Link, with target frame.
     *
     * @param link String name of the file.
     * @param target Name of the target frame.
     * @param label Tag for the link.
     */
    public void printTargetHyperLink(String link, String target, 
                                     String label) {
       printTargetHyperLink(link, "", target, label, false);
    }

    /**
     * Print Class link, with target frame.
     *
     * @param cd The class to which link is.
     * @param target Name of the target frame.
     */
    public void printTargetClassLink(ClassDoc cd, String target) {
        String filename = cd.name() + ".html";
        printTargetHyperLink(filename, target, 
                             (cd.isInterface() || cd.isAbstract())? //new
                                 italicsText(cd.name()): cd.name());
    }

    /**
     * Print Package link, with target frame.
     *
     * @param pd The link will be to the "package-summary.html" page for this 
     * package.
     * @param target Name of the target frame.
     * @param label Tag for the link.
     */
    public void printTargetPackageLink(PackageDoc pd, String target, 
                                       String label) {
        printTargetHyperLink(pathString(pd, "package-summary.html"), 
                             target, label);
    }
    /**
     * Print the html file header. Also print Html page title and stylesheet
     * default properties.
     * 
     * @param title String title for the generated html file.
     */
    public void printHeader(String title) {
        println("<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0 Frameset//EN\"" +
                "\"http://www.w3.org/TR/REC-html40/frameset.dtd\">");    
        println("<!--NewPage-->");
        html();
        head();
        print("<!-- Generated by javadoc on ");
        print(today());
        println(" -->");
        if (Standard.configuration().charset.length() > 0) {
            println("<META http-equiv=\"Content-Type\" content=\"text/html; " 
                    + "charset=" + Standard.configuration().charset + "\">");
        }
        title();
        println(title);
        titleEnd();
        printStyleSheetProperties();
        headEnd();
        body("white");
    }

    /**
     * Print user specified header and the footer.
     * 
     * @param header if true print the user provided header else print the
     * user provided footer.
     */
    public void printUserHeaderFooter(boolean header) {
        em();
        if (header) {
            print(replaceDocRootDir(Standard.configuration().header));
        } else {
            if (Standard.configuration().footer.length() != 0) {
                print(replaceDocRootDir(Standard.configuration().footer));
            } else {
                print(replaceDocRootDir(Standard.configuration().header));
	    }
        }
        emEnd();
    }

    /**
     * Print the user specified bottom.
     */ 
    public void printBottom() {
        hr();
        print(replaceDocRootDir(Standard.configuration().bottom)); 
    } 

    /**
     * Print the navigation bar for the Html page at the top and and the bottom.
     *
     * @param header If true print navigation bar at the top of the page else
     * print the nevigation bar at the bottom.
     */
    protected void navLinks(boolean header) {
        println("");
        println("<!-- ========== START OF NAVBAR ========== -->");
        if (!Standard.configuration().nonavbar) {
            if (header) {
                anchor("navbar_top");
            } else {
                anchor("navbar_bottom");
            }
            table(0, "100%", 1, 0);
            tr();
            tdColspanBgcolorStyle(2, "#EEEEFF", "NavBarCell1");
            println("");
            if (header) {
                anchor("navbar_top_firstrow");
            } else {
                anchor("navbar_bottom_firstrow");
            }
            table(0, 0, 3);
            print("  ");
            trAlignVAlign("center", "top");

	    if (Standard.configuration().createoverview) {
                navLinkContents();
            }

            if (Standard.configuration().packages.length > 0) {
                navLinkPackage();
            }

            navLinkClass();

            if(Standard.configuration().classuse) {
                navLinkClassUse();
            }
            if(Standard.configuration().createtree) {
                navLinkTree();
            }
            if(!(Standard.configuration().nodeprecated || 
                    Standard.configuration().nodeprecatedlist)) {
                navLinkDeprecated();
            }
            if(Standard.configuration().createindex) {
                navLinkIndex();
            }
            if (!Standard.configuration().nohelp) {
                navLinkHelp();
            }
            print("  ");
            trEnd();
            tableEnd();
            tdEnd();

            tdAlignVAlignRowspan("right", "top", 3);

            printUserHeaderFooter(header);
            tdEnd();
            trEnd();
            println("");

            tr();
            tdBgcolorStyle("white", "NavBarCell2");
            font("-2");
            space();
            navLinkPrevious();
            space();
            println("");
            space();
            navLinkNext();
            fontEnd();
            tdEnd();

            tdBgcolorStyle("white", "NavBarCell2");
            font("-2");
            print("  ");
            navShowLists();
            print("  ");
            space();
            println("");
            space();
            navHideLists();
            fontEnd();
            tdEnd();

            trEnd();
            
            printSummaryDetailLinks();

            tableEnd();
            println("<!-- =========== END OF NAVBAR =========== -->");
            println("");
        }
    }  

    /**
     * Do nothing. This is the default method. 
     */
    protected void printSummaryDetailLinks() {
    }

    /**
     * Print link to the "overview-summary.html" page.
     */
    protected void navLinkContents() {
        navCellStart();
        printHyperLink(relativepath + "overview-summary.html", "",
                       getText("doclet.Overview"), true, "NavBarFont1");
        navCellEnd();
    }
                                
    /**
     * Description for a cell in the navigation bar.
     */
    protected void navCellStart() {
        print("  ");
        tdBgcolorStyle("#EEEEFF", "NavBarCell1");
        print("    ");
    }

    /**
     * Description for a cell in the navigation bar, but with reverse 
     * high-light effect.
     */
    protected void navCellRevStart() {
        print("  ");
        tdBgcolorStyle("#FFFFFF", "NavBarCell1Rev");
        print(" ");
        space();
    }

    /**
     * Closing tag for navigation bar cell.
     */
    protected void navCellEnd() {
        space();
        tdEnd();
    }

    /**
     * Print link to the "package-summary.html" page for the package passed.
     *
     * @param pkg Package to which link will be generated.
     */
    protected void navLinkPackage(PackageDoc pkg) {
        printPackageLink(pkg, getFontColor("NavBarFont1") + getBold() + 
                         getText("doclet.Package") + 
                         getBoldEnd() + getFontEnd());
    }

    /**
     * Print the word "Package" in the navigation bar cell, to indicate that
     * link is not available here.
     */
    protected void navLinkPackage() {
        navCellStart();
        fontStyle("NavBarFont1");
        printText("doclet.Package");
        fontEnd();
        navCellEnd();
    }
                                
    /**
     * Print the word "Use" in the navigation bar cell, to indicate that link 
     * is not available.
     */
    protected void navLinkClassUse() {
        navCellStart();
        fontStyle("NavBarFont1");
        printText("doclet.navClassUse");
        fontEnd();
        navCellEnd();
    }
                                
    /**
     * Print link for previous file.
     *
     * @param prev File name for the prev link.
     */
    public void navLinkPrevious(String prev) {
        String tag = getText("doclet.Prev");
        if (prev != null) {
            printHyperLink(prev, "", tag, true) ;
        } else {
            print(tag);
        }
    }

    /**
     * Print the word "PREV" to indicate that no link is available.
     */
    protected void navLinkPrevious() {
        navLinkPrevious(null);
    }
                                
    /**
     * Print link for next file.
     *
     * @param next File name for the next link.
     */
    public void navLinkNext(String next) {
        String tag = getText("doclet.Next");
        if (next != null) {
            printHyperLink(next, "", tag, true);
        } else {
            print(tag);
        }
    }

    /**
     * Print the word "NEXT" to indicate that no link is available.
     */
    protected void navLinkNext() {
        navLinkNext(null);
    }
                                
    /**
     * Print "FRAMES" link, to switch to the frame version of the output.
     * 
     * @param link File to be linked, "index.html".
     */
    protected void navShowLists(String link) {
        printBoldTargetHyperLink(link, "_top", getText("doclet.FRAMES"));
    }
                                
    /**
     * Print "FRAMES" link, to switch to the frame version of the output.
     */
    protected void navShowLists() {
        navShowLists(relativepath + "index.html");
    }
                                
    /**
     * Print "NO FRAMES" link, to switch to the non-frame version of the output.
     * 
     * @param link File to be linked.
     */
    protected void navHideLists(String link) {
        printBoldTargetHyperLink(link, "_top", getText("doclet.NO_FRAMES"));
    }
                                
    /**
     * Print "NO FRAMES" link, to switch to the non-frame version of the output.
     */
    protected void navHideLists() {
        navHideLists(filename);
    }
         
    /**                       
     * Print "Tree" link in the navigation bar. If there is only one package 
     * specified on the command line, then the "Tree" link will be to the 
     * only "package-tree.html" file otherwise it will be to the 
     * "overview-tree.html" file.
     */
    protected void navLinkTree() { 
        navCellStart();
        PackageDoc[] packages = Standard.configuration().packages;
        if (packages.length == 1) {
            printHyperLink(pathString(packages[0], "package-tree.html"), "",
                           getText("doclet.Tree"), true, "NavBarFont1");
        } else {
            printHyperLink(relativepath + "overview-tree.html", "",
                           getText("doclet.Tree"), true, "NavBarFont1");
        }
        navCellEnd();
    }

    /**
     * Print "Tree" link to the "overview-tree.html" file.
     */
    protected void navLinkMainTree(String label) {
        printHyperLink(relativepath + "overview-tree.html", label);
    }
                                
    /**
     * Print the word "Class" in the navigation bar cell, to indicate that 
     * class link is not available.
     */
    protected void navLinkClass() {
        navCellStart();
        fontStyle("NavBarFont1");
        printText("doclet.Class");
        fontEnd();
        navCellEnd();
    }
                                
    /**
     * Print "Deprecated" API link in the navigation bar.
     */
    protected void navLinkDeprecated() {
        navCellStart();
        printHyperLink(relativepath + "deprecated-list.html", "",
                       getText("doclet.navDeprecated"), true, "NavBarFont1");
        navCellEnd();
    }
                                                                
    /**
     * Print link for generated index. If the user has used "-splitindex" 
     * command line option, then link to file "index-files/index-1.html" is
     * generated otherwise link to file "index-all.html" is generated.
     */
    protected void navLinkIndex() {
        navCellStart();
        printHyperLink(relativepath + 
                       (Standard.configuration().splitindex?
                            DirectoryManager.getPath("index-files") + 
                            fileseparator: "") + 
                       (Standard.configuration().splitindex?
                            "index-1.html" : "index-all.html"), "", 
                       getText("doclet.Index"), true, "NavBarFont1");
        navCellEnd();
    }

    /**
     * Print help file link. If user has provided a help file, then generate a 
     * link to the user given file, which is already copied to current or 
     * destination directory.
     */
    protected void navLinkHelp() {
        String helpfilenm = Standard.configuration().helpfile;
        if (helpfilenm.equals("")) {
            helpfilenm = "help-doc.html"; 
        } else {
            int lastsep;
            if ((lastsep = helpfilenm.lastIndexOf(File.separatorChar)) != -1) {
                helpfilenm = helpfilenm.substring(lastsep + 1);
            }
        } 
        navCellStart();
        printHyperLink(relativepath + helpfilenm, "", 
                       getText("doclet.Help"), true, "NavBarFont1");
        navCellEnd();
    }

    /**
     * Print the word "Detail" in the navigation bar. No link is available.
     */
    protected void navDetail() {
        printText("doclet.Detail");
    }

    /**
     * Print the word "Summary" in the navigation bar. No link is available.
     */                             
    protected void navSummary() {
        printText("doclet.Summary");
    }
   
    /**                             
     * Print the Html table tag for the index summary tables. The table tag
     * printed is 
     * <TABLE BORDER="1" CELLPADDING="3" "CELLSPACING="0" WIDTH="100%">
     */
    public void tableIndexSummary() {
        println("\n<TABLE BORDER=\"1\" CELLPADDING=\"3\" " + 
                "CELLSPACING=\"0\" WIDTH=\"100%\">");
    }

    /**                             
     * Same as {@link #tableIndexSummary()}.
     */
    public void tableIndexDetail() {
        println("\n<TABLE BORDER=\"1\" CELLPADDING=\"3\" " + 
                "CELLSPACING=\"0\" WIDTH=\"100%\">");
    }

    /**
     * Print Html tag for table elements. The tag printed is
     * <TD ALIGN="right" VALIGN="top" WIDTH="1%">.
     */
    public void tdIndex() {
        print("<TD ALIGN=\"right\" VALIGN=\"top\" WIDTH=\"1%\">");
    }

    /**
     * Prine table header information about color, column span and the font.
     *
     * @param color Background color.
     * @param span  Column span.
     */
    public void tableHeaderStart(String color, int span) {
        trBgcolorStyle(color, "TableHeadingColor");
        tdColspan(span);
        font("+2");
    }

    /**
     * Print table header for the inherited members summary tables. Print the
     * background color information.
     *
     * @param color Background color.
     */
    public void tableInheritedHeaderStart(String color) {
        trBgcolorStyle(color, "TableSubHeadingColor");
        td();
    }

    /**
     * Print "Use" table header. Print the background color and the column span.
     *
     * @param color Background color.
     */
    public void tableUseInfoHeaderStart(String color) {
        trBgcolorStyle(color, "TableSubHeadingColor");
        tdColspan(2);
    }
    
    /**
     * Print table header with the background color with default column span 2.
     *
     * @param color Background color.
     */
    public void tableHeaderStart(String color) {
        tableHeaderStart(color, 2);
    }
 
    /**
     * Print table header with the column span, with the default color #CCCCFF.
     *
     * @param span Column span.
     */   
    public void tableHeaderStart(int span) {
        tableHeaderStart("#CCCCFF", span);
    }
  
    /**
     * Print table header with default column span 2 and default color #CCCCFF.
     */       
    public void tableHeaderStart() {
        tableHeaderStart(2);
    }

    /**
     * Print table header end tags for font, column and row.
     */   
    public void tableHeaderEnd() {
        fontEnd();
        tdEnd();
        trEnd();
    }

    /**
     * Print table header end tags in inherited tables for column and row.
     */  
    public void tableInheritedHeaderEnd() {
        tdEnd();
        trEnd();
    }

    /**
     * Print the summary table row cell attribute width.
     *
     * @param width Width of the table cell.
     */
    public void summaryRow(int width) {
         if (width != 0) {
             tdWidth(width + "%");
         } else {
             td();
         }
    } 

    /**
     * Print the summary table row cell end tag.
     */       
    public void summaryRowEnd() {
         tdEnd();
    } 

    /**       
     * Print the heading in Html <H2> format.
     * 
     * @param str The Header string.
     */
    public void printIndexHeading(String str) {
        h2();
        print(str);
        h2End();
    } 

    /**
     * Print Html tag <FRAMESET=arg>.
     * 
     * @param arg Argument for the tag.
     */
    public void frameSet(String arg) {
        println("<FRAMESET " + arg + ">");
    }

    /**
     * Print Html closing tag </FRAMESET>.
     */
    public void frameSetEnd() {
        println("</FRAMESET>");
    }

    /**
     * Print Html tag <FRAME=arg>.
     * 
     * @param arg Argument for the tag.
     */
    public void frame(String arg) {
        println("<FRAME " + arg + ">");
    }

    /**
     * Print Html closing tag </FRAME>.
     */
    public void frameEnd() {
        println("</FRAME>");
    }

    /**
     * Return path to the class page for a classdoc. For example, the class 
     * name is "java.lang.Object" and if the current file getting generated is
     * "java/io/File.html", then the path string to the class, returned is 
     * "../../java/lang.Object.html".
     * 
     * @param cd Class to which the path is requested.
     */
    protected String pathToClass(ClassDoc cd) {
        return pathString(cd.containingPackage(), cd.name() + ".html");
    }

    /**
     * Return the path to the class page for a classdoc. Works same as 
     * {@link #pathToClass(ClassDoc)}.
     *
     * @param cd   Class to which the path is requested.
     * @param name Name of the file(doesn't include path).
     */
    protected String pathString(ClassDoc cd, String name) {
        return pathString(cd.containingPackage(), name);
    }

    /**
     * Return path to the given file name in the given package. So if the name
     * passed is "Object.html" and the name of the package is "java.lang", and
     * if the relative path is "../.." then returned string will be
     * "../../java/lang/Object.html"
     *
     * @param pd Package in which the file name is assumed to be.
     * @param name File name, to which path string is.
     */
    protected String pathString(PackageDoc pd, String name) {
        StringBuffer buf = new StringBuffer(relativepath);
        buf.append(DirectoryManager.getPathToPackage(pd, name));
        return buf.toString();
    }

    /**
     * Print link to the "pacakge-summary.html" file, depending upon the 
     * package name.
     */
    public void printPackageLink(PackageDoc pkg) {
        print(getPackageLink(pkg));
    }

    public void printPackageLink(PackageDoc pkg, boolean bold) {
        print(getPackageLink(pkg, bold));
    }

    public void printPackageLink(PackageDoc pkg, String linklabel) {
        print(getPackageLink(pkg, linklabel, false));
    }

    /**
     * Get link for individual package file.
     */
    public String getPackageLink(PackageDoc pkg) {
        return getPackageLink(pkg, pkg.name(), false);
    }

    public String getPackageLink(PackageDoc pkg, boolean bold) {
        return getPackageLink(pkg, pkg.name(), bold);
    }

    public String getPackageLink(PackageDoc pkg, String label) {
        return getPackageLink(pkg, label, false);
    }

    public String getPackageLink(PackageDoc pkg, String linklabel, 
                                 boolean bold) {
        if (pkg.isIncluded()) {
            return getHyperLink(pathString(pkg, "package-summary.html"), 
                                           "", linklabel, bold);
        } else {
            String crossPkgLink = getCrossPackageLink(pkg.name());
            if (crossPkgLink != null) {
                return getHyperLink(crossPkgLink, "", linklabel, bold);
            } else {
                return linklabel;
            }
        }
    }

    public String italicsClassName(ClassDoc cd, boolean qual) {
        String name = (qual)? cd.qualifiedName(): cd.name();
        return (cd.isInterface())?  italicsText(name): name;
    }
       
    public void printClassLinkForSameDir(ClassDoc cd) {
        if (cd.isIncluded()) {
 	    if (isGeneratedDoc(cd)) {
                printHyperLink(cd.name() + ".html", "", 
                               italicsClassName(cd, false));
                return;
            }
        } 
        print(italicsClassName(cd, true));
    } 

    public void printClassLink(ClassDoc cd) {
        print(getClassLink(cd, false));
    }

    public String getClassLink(ClassDoc cd) {
        return getClassLink(cd, false);
    }

    public void printClassLink(ClassDoc cd, String label) {
        print(getClassLink(cd, "", label, false));
    }

    public String getClassLink(ClassDoc cd, String label) {
        return getClassLink(cd, "", label, false);
    }

    public void printClassLink(ClassDoc cd, String where, String label) {
        print(getClassLink(cd, where, label, false));
    }

    public void printClassLink(ClassDoc cd, String label, boolean bold) {
        print(getClassLink(cd, "", label, bold));
    }

    public void printClassLink(ClassDoc cd, String where, String label, 
                               boolean bold, String color) {
        print(getClassLink(cd, where, label, bold, color));
    }

    public String getClassLink(ClassDoc cd, String where, String label) {
        return getClassLink(cd, where, label, false);
    }

    public void printClassLink(ClassDoc cd, boolean bold) {
        print(getClassLink(cd, bold));
    }

    public String getClassLink(ClassDoc cd, boolean bold) {
        return getClassLink(cd, "", "", bold);
    }

    public void printClassLink(ClassDoc cd, String where, 
                               String label, boolean bold) {
        print(getClassLink(cd, where, label, bold));
    }

    public String getClassLink(ClassDoc cd, String where,
                               String label, boolean bold, String color) {
        boolean nameUnspecified = label.length() == 0;
        if (nameUnspecified) {
            label = cd.name();
        }       
        displayLength += label.length();
        if (cd.isIncluded()) {
            if (isGeneratedDoc(cd)) {
                String filename = pathToClass(cd);
                return getHyperLink(filename, where, label, bold, color);
            }
        } else {
            String crosslink = getCrossClassLink(cd);
            if (crosslink != null) {
                return getHyperLink(crosslink, where, label, bold, color);
            }
        }
        if (nameUnspecified) {
            displayLength -= label.length();
            label = cd.qualifiedName();
            displayLength += label.length();
        }            
        return label;
    }

    public String getClassLink(ClassDoc cd, String where,
                               String label, boolean bold) {
        return getClassLink(cd, where, label, bold, "");
    }

    public String getCrossClassLink(ClassDoc cd) {
        return getCrossLink(cd.containingPackage().name(), 
                            cd.name() + ".html");
    }

    public boolean isCrossClassIncluded(ClassDoc cd) {
        if (cd.isIncluded()) {
  	    return isGeneratedDoc(cd);
        }
        return Extern.findPackage(cd.containingPackage().name()) != null; 
    }
 
    public String getCrossPackageLink(String packagename) {
        return getCrossLink(packagename, "package-summary.html");
    }

    public String getCrossLink(String packagename, String link) {
        Extern fnd = Extern.findPackage(packagename);
        if (fnd != null) {
            String externlink = fnd.path + link;
            if (fnd.relative) {  // it's a relative path.
                return relativepath + externlink;
            } else {  
                return externlink; 
            }
        }
        return null;
    }

    public void printQualifiedClassLink(ClassDoc cd) {
        printClassLink(cd, "", cd.qualifiedName());
    }

    public String getQualifiedClassLink(ClassDoc cd) {
        return getClassLink(cd, "", cd.qualifiedName());
    }

    /**
     * Print Class link, with only class name as the link and prefixing
     * plain package name.
     */
    public void printPreQualifiedClassLink(ClassDoc cd) {
        print(getPreQualifiedClassLink(cd, false));
    }

    public String getPreQualifiedClassLink(ClassDoc cd) {
        return getPreQualifiedClassLink(cd, false);
    }

    public String getPreQualifiedClassLink(ClassDoc cd, boolean bold) {
        String classlink = getPkgName(cd);
        classlink += getClassLink(cd, "", cd.name(), bold);
        return classlink; 
    }
    
    
    /**
     * Print Class link, with only class name as the bold link and prefixing
     * plain package name.
     */
    public void printPreQualifiedBoldClassLink(ClassDoc cd) {
        print(getPreQualifiedClassLink(cd, true));
    }

    public void printText(String key) {
        print(getText(key));
    }

    public void printText(String key, String a1) {
        print(getText(key, a1));
    }

    public void printText(String key, String a1, String a2) {
        print(getText(key, a1, a2));
    }

    public void boldText(String key) {
        bold(getText(key));
    }

    public void boldText(String key, String a1) {
        bold(getText(key, a1));
    }

    public void boldText(String key, String a1, String a2) {
        bold(getText(key, a1, a2));
    }

    public String getText(String key) {
        return Standard.configuration().standardmessage.getText(key);
    }

    public String getText(String key, String a1) {
        return Standard.configuration().standardmessage.getText(key, a1);
    }

    public String getText(String key, String a1, String a2) {
        return Standard.configuration().standardmessage.getText(key, a1, a2);
    }

    public String getText(String key, String a1, String a2, String a3) {
        return Standard.configuration().standardmessage.getText(key, a1, 
                                                                a2, a3);
    }

    public void notice(String key, String a1) {
        Standard.configuration().standardmessage.notice(key, a1);
    }

    public void notice(String key, String a1, String a2) {
        Standard.configuration().standardmessage.notice(key, a1, a2);
    }

    public void warning(String key, String a1) {
        Standard.configuration().standardmessage.warning(key, a1);
    }

    public void warning(String key, String a1, String a2) {
        Standard.configuration().standardmessage.warning(key, a1, a2);
    }

    public void error(String key, String a1) {
        Standard.configuration().standardmessage.notice(key, a1);
    }

    public void error(String key, String a1, String a2) {
        Standard.configuration().standardmessage.notice(key, a1, a2);
    }

    /**
     * Print link for any doc element.
     */
    public void printDocLink(Doc doc, String label, boolean bold) {
        print(getDocLink(doc, label, bold));
    }

    public String getDocLink(Doc doc, String label, boolean bold) {
        if (!doc.isIncluded() || !isGeneratedDoc(doc)) {
            return label;
        }
        if (doc instanceof PackageDoc) {
            return getPackageLink((PackageDoc)doc, label);
        } else if (doc instanceof ClassDoc) {
            return getClassLink((ClassDoc)doc, "", label, bold);
        } else if (doc instanceof ExecutableMemberDoc) {
            ExecutableMemberDoc emd = (ExecutableMemberDoc)doc;
            return getClassLink(emd.containingClass(),  
                                emd.name()+emd.signature(), label, bold);
        } else if (doc instanceof MemberDoc) {
            MemberDoc md = (MemberDoc)doc;
            return getClassLink(md.containingClass(), md.name(), label, bold);
        } else if (doc instanceof RootDoc) {
            return getHyperLink("overview-summary.html", label);
        } else {
            return label;
        }
    }

    /**
     * Return true if the doc element is getting documented, depending upon 
     * -nodeprecated option and @deprecated tag used. Return true if 
     * -nodeprecated is not used or @deprecated tag is not used.
     */ 
    public boolean isGeneratedDoc(Doc doc) {
        return Standard.isGeneratedDoc(doc);
    }

    public void printDocLink(Doc doc, String label) {
        printDocLink(doc, label, false);
    } 

    public String getDocLink(Doc doc, String label) {
        return getDocLink(doc, label, false);
    } 

   /**
     * Print the see tags information given the doc comment.
     *
     * @param doc Doc doc
     * @see com.sun.javadoc.Doc
     */
    public void printSeeTags(Doc doc) {
       SeeTag[] sees = doc.seeTags();
       if (sees.length > 0) {
            dt();
            boldText("doclet.See_Also");
            dd();
            for (int i = 0; i < sees.length; ++i) {
                if (i > 0) {
                    println(", ");
                }
                printSeeTag(sees[i]);
            }
        }
        if (doc.isClass() && ((ClassDoc)doc).isSerializable()) {
            if (sees.length > 0) {
                print(", ");
            } else {
                dt();
                boldText("doclet.See_Also");
                dd();
            }   
            printHyperLink(relativepath + "serialized-form.html", 
                           ((ClassDoc)(doc)).qualifiedName(),
                           getText("doclet.Serialized_Form")); 
        }
    }
               
    public void printSeeTag(SeeTag see) {
        PackageDoc refPackage = see.referencedPackage();
        ClassDoc refClass = see.referencedClass();
        String refClassName = see.referencedClassName();
        String refPackName = refClassName;
        MemberDoc refMem = see.referencedMember();
        String refMemName = see.referencedMemberName();
        String label = see.label();
        label = (label.length() > 0)? getCode() + label + getCodeEnd():"";
        String seetext = see.text();
        String text = getCode() + seetext + getCodeEnd();
        if (seetext.startsWith("<") || seetext.startsWith("\"")) {
            print(seetext);
            return;
        }
        if (refClass == null) {
            if (refPackage != null && refPackage.isIncluded()) { 
                printPackageLink(refPackage);
            } else {
                // getCrossPackageLink for package
                if (refPackName != null && refPackName.length() > 0) {
                    String crosslink = getCrossPackageLink(refPackName);
                    if (crosslink != null) {
                        printHyperLink(crosslink, "", refPackName, false);
                    } else {  
                        warning("doclet.see.class_or_package_not_found", 
                                                        see.name(), seetext);
                        print((label.length() == 0)? text: label);
                    }
                } else {
                    error("doclet.see.malformed_tag", see.name(), seetext);
                }
            } 
        } else if (refMemName == null) {
            // class reference
            if (label.length() == 0) {
                label = getCode() + refClass.name() + getCodeEnd();
                printClassLink(refClass, label); 
            } else {
                printClassLink(refClass, (label.length() == 0)? text: label);
            }
        } else if (refMem == null) {
            // can't find the member reference
            print((label.length() == 0)? text: label);
        } else {
            // member reference
            ClassDoc containing = refMem.containingClass();
            if (currentcd != containing) {
                refMemName = containing.name() + "." + refMemName;
            }
            if (refMem instanceof ExecutableMemberDoc) {
                if (refMemName.indexOf('(') < 0) {
                    refMemName += ((ExecutableMemberDoc)refMem).signature();
                }
            } 
            text = getCode() + refMemName + getCodeEnd();
            printDocLink(refMem, (label.length() == 0)? text: label);
        }
    }  

    public void generateTagInfo(Doc doc) { //new
	generateTagInfo(doc, null);
    }

    /**
     * Print tag information
     */
    public void generateTagInfo(Doc doc, String path) { //new
        Tag[] sinces = doc.tags("since");
        Tag[] sees = doc.seeTags();
        Tag[] authors;
        Tag[] versions;
        if (Standard.configuration().showauthor) {
            authors = doc.tags("author");
        } else {
            authors = new Tag[0];
        }
        if (Standard.configuration().showversion) {
            versions = doc.tags("version");
        } else {
            versions = new Tag[0];
        }
        if (Standard.configuration().nosince) {
            sinces = new Tag[0];
        }
        if (sinces.length > 0
            || sees.length > 0
            || authors.length > 0
            || versions.length > 0 
            || (doc.isClass() && ((ClassDoc)doc).isSerializable())
	    || Standard.configuration().linksources) { //new
            dl();
            printSinceTag(doc);
            if (versions.length > 0) {
                // There is going to be only one Version tag.
                dt();
                boldText("doclet.Version");
                dd();
                printInlineComment(versions[0]);
                ddEnd();
            }
            if (authors.length > 0) {
                dt();
                boldText("doclet.Author");
                dd();
                for (int i = 0; i < authors.length; ++i) {
                    if (i > 0) {
                        print(", ");
                    } 
                    printInlineComment(authors[i]);
                }
                ddEnd();
            }
            printSeeTags(doc);
	    //new passage
	    if (Standard.configuration().linksources && path != null){
                dt();
                boldText("doclet.Source_Code");
                String fileName = relativepath;
                String fileSuffix = path.substring(path.lastIndexOf('.'));
                String docName = doc.name();
                // handle inner classes
                int p = docName.indexOf('.');
                if (p >= 0) {
                    docName = docName.substring(0, p);
                    p = path.lastIndexOf(File.separatorChar);
                    fileName += path.substring(0, p) + fileSuffix;
                } else {
                    fileName += path;
                }
                docName += fileSuffix;
                dd();
                printHyperLink(fileName, docName);
                ddEnd();
            }
	    //new passage end

            dlEnd();
        }
    }


    public void printSinceTag(Doc doc) {
        Tag[] sinces = doc.tags("since");
        if (!Standard.configuration().nosince && sinces.length > 0) {  
            // there is going to be only one since tag
            dt();
            boldText("doclet.Since");
            dd();
            printInlineComment(sinces[0]);
            ddEnd();
        } 
    }       

    public void printInlineComment(Tag tag) {
        printCommentTags(tag.inlineTags(), false, false);
    }

    public void printInlineDeprecatedComment(Tag tag) {
        printCommentTags(tag.inlineTags(), true, false);
    }
    
    public void printSummaryComment(Doc doc) {
        printCommentTags(doc.firstSentenceTags(), false, true);
    }
    
    public void printSummaryDeprecatedComment(Doc doc) {
        printCommentTags(doc.firstSentenceTags(), true, true);
    }
    
    public void printSummaryDeprecatedComment(Tag tag) {
        printCommentTags(tag.firstSentenceTags(), true, true);
    }
    
    public void printInlineComment(Doc doc) {
        printCommentTags(doc.inlineTags(), false, false);
    }
    
    public void printInlineDeprecatedComment(Doc doc) {
        printCommentTags(doc.inlineTags(), true, false);
    }
    
    private void printCommentTags(Tag[] tags, boolean depr, boolean first) {
        if (depr) {
            italic();
        }
        for (int i = 0; i < tags.length; i++) {
            Tag tagelem = tags[i];
            if (tagelem instanceof SeeTag) {
                printSeeTag((SeeTag)tagelem);
            } else {
                String text = tagelem.text(); 
                text = replaceDocRootDir(text);
                if (first) {
                    text = removeNonInlineTags(text);
                } 
                print(text);
            }
        }
        if (depr) {
            italicEnd();
        }
        if (tags.length == 0) {
            space();
        }
    }

    public String removeNonInlineTags(String text) {
        if (text.indexOf('<') < 0) {
            return text;
        }
        String noninlinetags[] = { "<ul>", "</ul>", "<ol>", "</ol>", 
                                   "<dl>", "</dl>", "<table>", "</table>", 
                                   "<tr>", "</tr>", "<td>", "</td>", 
                                   "<th>", "</th>", "<p>", "</p>", 
                                   "<li>", "</li>", "<dd>", "</dd>", 
                                   "<dir>", "</dir>", "<dt>", "</dt>", 
                                   "<h1>", "</h1>", "<h2>", "</h2>", 
                                   "<h3>", "</h3>", "<h4>", "</h4>", 
                                   "<h5>", "</h5>", "<h6>", "</h6>", 
                                   "<pre>", "</pre>", "<menu>", "</menu>", 
                                   "<listing>", "</listing>", "<hr>", 
                                   "<blockquote>", "</blockquote>", 
                                   "<center>", "</center>",
                                   "<UL>", "</UL>", "<OL>", "</OL>", 
                                   "<DL>", "</DL>", "<TABLE>", "</TABLE>", 
                                   "<TR>", "</TR>", "<TD>", "</TD>", 
                                   "<TH>", "</TH>", "<P>", "</P>", 
                                   "<LI>", "</LI>", "<DD>", "</DD>", 
                                   "<DIR>", "</DIR>", "<DT>", "</DT>", 
                                   "<H1>", "</H1>", "<H2>", "</H2>", 
                                   "<H3>", "</H3>", "<H4>", "</H4>", 
                                   "<H5>", "</H5>", "<H6>", "</H6>", 
                                   "<PRE>", "</PRE>", "<MENU>", "</MENU>", 
                                   "<LISTING>", "</LISTING>", "<HR>", 
                                   "<BLOCKQUOTE>", "</BLOCKQUOTE>", 
                                   "<CENTER>", "</CENTER>" 
                                 };
        for (int i = 0; i < noninlinetags.length; i++) {
            text = replace(text, noninlinetags[i], ""); 
        }
        return text;
    }

    public String replace(String text, String tobe, String by) {
        while (true) {
            int startindex = text.indexOf(tobe);
            if (startindex < 0) {
                return text;
            }
            int endindex = startindex + tobe.length();
            StringBuffer replaced = new StringBuffer();
            if (startindex > 0) {
                replaced.append(text.substring(0, startindex));
            }
            replaced.append(by);
            if (text.length() > endindex) {
                replaced.append(text.substring(endindex)); 
            }
            text = replaced.toString();
        }
    }
 
    public void printStyleSheetProperties() {
        String filename = Standard.configuration().stylesheetfile;
        if (filename.length() > 0) {
            File stylefile = new File(filename);
            String parent = stylefile.getParent();
            filename = (parent == null)? 
                            filename:
                            filename.substring(parent.length() + 1);
        } else {
            filename = "stylesheet.css";
        }
        filename = relativepath + filename;
        link("REL =\"stylesheet\" TYPE=\"text/css\" HREF=\"" +
              filename + "\" " + "TITLE=\"Style\"");
    }

    /**
     * According to the Java Language Specifications, all the outer classes
     * and static inner classes are core classes.
     */
    public boolean isCoreClass(ClassDoc cd) {
        return cd.containingClass() == null || cd.isStatic();
    }

}
