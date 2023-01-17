/*
 * @(#)StylesheetWriter.java	1.11 00/02/02
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
 *
 * @author Atul M Dambalkar
 */
public class StylesheetWriter extends HtmlStandardWriter {

    /**
     * Constructor.
     */
    public StylesheetWriter(String filename) throws IOException {
        super(filename);
    }

    /**
     * Generate the style file contents.
     */
    public static void generate() throws DocletAbortException {
        StylesheetWriter stylegen;
        String filename = "";
        try {
            filename = "stylesheet.css";
            stylegen = new StylesheetWriter(filename);
            stylegen.generateStyleFile();
            stylegen.close();
        } catch (IOException exc) {
            Standard.configuration().standardmessage.error(
                "doclet.exception_encountered",
                exc.toString(), filename);
            throw new DocletAbortException();
        }
    }

    /**
     * Generate the style file contents.
     */
    protected void generateStyleFile() {
        print("/* "); printText("doclet.Style_line_1"); println(" */");
        println("");
        print("/* "); printText("doclet.Style_line_2"); println(" */");
        println("");
        print("/* "); printText("doclet.Style_line_3"); println(" */");
        println("body { background-color: #FFFFFF }"); println("");
        print("/* "); printText("doclet.Style_line_4"); println(" */");
        print(".TableHeadingColor     { background: #CCCCFF }"); 
        print(" /* "); printText("doclet.Style_line_5"); println(" */");
        print(".TableSubHeadingColor  { background: #EEEEFF }"); 
        print(" /* "); printText("doclet.Style_line_6"); println(" */");
        print(".TableRowColor         { background: #FFFFFF }"); 
        print(" /* "); printText("doclet.Style_line_7"); println(" */");
        println("");
        print("/* "); printText("doclet.Style_line_8"); println(" */");
        println(".FrameTitleFont   { font-size: normal; font-family: normal }");
        println(".FrameHeadingFont { font-size: normal; font-family: normal }");
        println(".FrameItemFont    { font-size: normal; font-family: normal }");
        println("");
        print("/* "); printText("doclet.Style_line_9"); println(" */");
        print("/* "); 
        print(".FrameItemFont  { font-size: 10pt; font-family: ");
        print("Helvetica, Arial, sans-serif }"); println(" */");
        println("");
        print("/* "); printText("doclet.Style_line_10"); println(" */");
        print(".NavBarCell1    { background-color:#EEEEFF;}");
        print("/* "); printText("doclet.Style_line_6"); println(" */");
        print(".NavBarCell1Rev { background-color:#00008B;}");
        print("/* "); printText("doclet.Style_line_11"); println(" */");

        print(".NavBarFont1    { font-family: Arial, Helvetica, sans-serif; ");
        println("color:#000000;}");
        print(".NavBarFont1Rev { font-family: Arial, Helvetica, sans-serif; ");
        println("color:#FFFFFF;}");
        println("");
        print(".NavBarCell2    { font-family: Arial, Helvetica, sans-serif; ");
        println("background-color:#FFFFFF;}");
        print(".NavBarCell3    { font-family: Arial, Helvetica, sans-serif; ");
        println("background-color:#FFFFFF;}");
        println("");

    }

}



