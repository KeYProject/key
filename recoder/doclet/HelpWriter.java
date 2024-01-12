/*
 * @(#)HelpWriter.java	1.12 00/02/02
 *
 * Copyright 1998-2000 Sun Microsystems, Inc. All Rights Reserved.
 * 
 * This software is the proprietary information of Sun Microsystems, Inc.  
 * Use is subject to license terms.
 * 
 */



import com.sun.tools.doclets.*;
import java.io.*;
import java.lang.*;
import java.util.*;

/**
 * Generate the Help File for the generated API documentation. The help file
 * contents are helpful for browsing the generated documentation.
 *
 * @author Atul M Dambalkar
 */
public class HelpWriter extends HtmlStandardWriter {

    /**
     * Constructor to construct HelpWriter object. 
     * @param filename File to be generated.
     */
    public HelpWriter(String filename) throws IOException {
        super(filename);
    }

    /**
     * Construct the HelpWriter object and then use it to generate the help 
     * file. The name of the generated file is "help-doc.html". The help file
     * will get generated if and only if "-helpfile" and "-nohelp" is not used
     * on the command line.
     */
    public static void generate() throws DocletAbortException {
        HelpWriter helpgen;
        String filename = "";
        try {
            filename = "help-doc.html";
            helpgen = new HelpWriter(filename);
            helpgen.generateHelpFile();
            helpgen.close();
        } catch (IOException exc) {
            Standard.configuration().standardmessage.error(
                "doclet.exception_encountered",
                exc.toString(), filename);
            throw new DocletAbortException();
        }
    }

    /**
     * Generate the help file contents.
     */
    protected void generateHelpFile() {
        printHeader(getText("doclet.Window_Help_title",
                            Standard.configuration().windowtitle));
        navLinks(true);  hr();

        printHelpFileContents();

        navLinks(false);
        printBottom();
        printBodyHtmlEnd();
    }

    /**
     * Print the help file contents from the resource file. While generating the
     * help file contents it also keeps track of user options. If "-notree" 
     * is used, then the "overview-tree.html" will not get generated and hence
     * help information also will not get generated.
     */
    protected void printHelpFileContents() {
        center(); h1(); printText("doclet.Help_line_1"); h1End(); centerEnd();
        printText("doclet.Help_line_2");
        if (Standard.configuration().createoverview) {
            h3(); printText("doclet.Overview"); h3End();
            blockquote(); p(); 
            printText("doclet.Help_line_3",
                       getHyperLink("overview-summary.html", 
                                     getText("doclet.Overview"))); 
            blockquoteEnd();
        }
        h3(); printText("doclet.Package"); h3End();
        blockquote(); p(); printText("doclet.Help_line_4"); 
        ul(); 
        li(); printText("doclet.Interfaces_Italic");
        li(); printText("doclet.Classes");
        li(); printText("doclet.Exceptions");
        li(); printText("doclet.Errors");
        ulEnd();
        blockquoteEnd();
        h3(); printText("doclet.Help_line_5"); h3End();
        blockquote(); p(); printText("doclet.Help_line_6");
        ul();
        li(); printText("doclet.Help_line_7");
        li(); printText("doclet.Help_line_8");
        li(); printText("doclet.Help_line_9");
        li(); printText("doclet.Help_line_10");
        li(); printText("doclet.Help_line_11");
        li(); printText("doclet.Help_line_12");
        p();
        li(); printText("doclet.Inner_Class_Summary");
        li(); printText("doclet.Field_Summary");
        li(); printText("doclet.Constructor_Summary");
        li(); printText("doclet.Method_Summary");
        p();
        li(); printText("doclet.Field_Detail");
        li(); printText("doclet.Constructor_Detail");
        li(); printText("doclet.Method_Detail");
        ulEnd(); 
        printText("doclet.Help_line_13");
        blockquoteEnd();
        if (Standard.configuration().classuse) {
            h3(); printText("doclet.Help_line_14"); h3End();
            blockquote(); 
            printText("doclet.Help_line_15");
            blockquoteEnd();
        }
        if (Standard.configuration().createtree) {
            h3(); printText("doclet.Help_line_16"); h3End();
            blockquote(); 
            printText("doclet.Help_line_17_with_tree_link",
                 getHyperLink("overview-tree.html", 
                               getText("doclet.Class_Hierarchy"))); 
            ul(); 
            li(); printText("doclet.Help_line_18");
            li(); printText("doclet.Help_line_19");
            ulEnd(); 
            blockquoteEnd();
        }
        if (!(Standard.configuration().nodeprecatedlist ||
                  Standard.configuration().nodeprecated)) {
            h3(); printText("doclet.Deprecated_API"); h3End();
            blockquote();
            printText("doclet.Help_line_20_with_deprecated_api_link",
                          getHyperLink("deprecated-list.html", 
                                        getText("doclet.Deprecated_API"))); 
            blockquoteEnd();
        }
        if (Standard.configuration().createindex) {
            String indexlink;
            if (Standard.configuration().splitindex) {
                indexlink = getHyperLink("index-files/index-1.html", 
                                          getText("doclet.Index"));
            } else {
                indexlink = getHyperLink("index-all.html", 
                                          getText("doclet.Index"));
            }
            h3(); printText("doclet.Help_line_21"); h3End();
            blockquote();
            printText("doclet.Help_line_22", indexlink);
            blockquoteEnd();
        }
        h3(); printText("doclet.Help_line_23"); h3End(); 
        printText("doclet.Help_line_24");
        h3(); printText("doclet.Help_line_25"); h3End(); 
        printText("doclet.Help_line_26"); p();
        h3(); printText("doclet.Serialized_Form"); h3End();
        printText("doclet.Help_line_27"); p(); 
        font("-1"); em(); 
        printText("doclet.Help_line_28"); 
        emEnd(); fontEnd(); br();
        hr();
    }

    /**
     * Highlight the word "Help" in the navigation bar as this is the help file.
     */
    protected void navLinkHelp() {
        navCellRevStart();
        fontStyle("NavBarFont1Rev");
        boldText("doclet.Help");
        fontEnd();
        navCellEnd();
    }
}



