/*
 * @(#)FrameOutputWriter.java	1.21 00/02/02
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
 * Generate the documentation in the Html "frame" format in the browser. The
 * generated documentation will have two or three frames depending upon the 
 * number of packages on the command line. In general there will be three frames
 * in the output, a left-hand top frame will have a list of all packages with
 * links to target left-hand bottom frame. The left-hand bottom frame will have
 * the particular package contents or the all-classes list, where as the single
 * right-hand frame will have overview or package summary or class file. Also
 * take care of browsers which do not support Html frames.
 *
 * @author Atul M Dambalkar 
 */
public class FrameOutputWriter extends HtmlStandardWriter {

    /**
     * Number of packages specified on the command line.
     */
    int noOfPackages;
  
    /**
     * Constructor to construct FrameOutputWriter object.
     *
     * @param filename File to be generated.
     */
    public FrameOutputWriter(String filename) throws IOException {
        super(filename);
	noOfPackages = Standard.configuration().packages.length;
    }

    /**
     * Construct FrameOutputWriter object and then use it to generate the Html
     * file which will have the description of all the frames in the
     * documentation. The name of the generated file is "index.html" which is
     * the default first file for Html documents.
     */
    public static void generate() throws DocletAbortException {
        FrameOutputWriter framegen;
        String filename = "";
        try {
            filename = "index.html";
            framegen = new FrameOutputWriter(filename);
            framegen.generateFrameFile();
            framegen.close();
        } catch (IOException exc) {
            Standard.configuration().standardmessage.error(
                "doclet.exception_encountered",
                exc.toString(), filename);
            throw new DocletAbortException();
        }
    }

    /**
     * Generate the contants in the "index.html" file. Print the frame details
     * as well as warning if browser is not supporting the Html frames.
     */
    protected void generateFrameFile() {
        if (Standard.configuration().windowtitle.length() > 0) { 
            printPartialHeader(Standard.configuration().windowtitle);     
        } else {
            printPartialHeader(getText("doclet.Generated_Docs_Untitled")); 
        }
        printFrameDetails();
        printFrameWarning();
        printFrameFooter();
    }

    /**
     * Generate the code for issueing the warning for a non-frame capable web 
     * client. Also provide links to the non-frame version documentation.
     */
    protected void printFrameWarning() {
        noFrames();
        h2();
        printText("doclet.Frame_Alert");
        h2End();
        p();
        printText("doclet.Frame_Warning_Message");
        br();
        printText("doclet.Link_To");
        printHyperLink(Standard.configuration().topFile, 
                       getText("doclet.Non_Frame_Version"));
        noFramesEnd();
    }

    /**
     * Print the frame sizes and their contents.
     */
    protected void printFrameDetails() {
        frameSet("cols=\"20%,80%\"");
        if (noOfPackages <= 1) {
            frame("src=\"" + "allclasses-frame.html" 
                  + "\" name=\"packageFrame\"");
            frame("src=\"" + Standard.configuration().topFile + 
                  "\" name=\"classFrame\"");
        } else if (noOfPackages > 1) {
            frameSet("rows=\"30%,70%\"");
            frame("src=\"overview-frame.html\" name=\"packageListFrame\"");
            frame("src=\"" + "allclasses-frame.html" 
                  + "\" name=\"packageFrame\"");
            frameSetEnd();
            frame("src=\"" + Standard.configuration().topFile + 
                  "\" name=\"classFrame\"");
        }
        frameSetEnd();
    }

}



