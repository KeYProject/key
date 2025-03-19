/*
 * @(#)SingleIndexWriter.java	1.10 00/02/02
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
 * Generate only one index file for all the Member Names with Indexing in 
 * Unicode Order. The name of the generated file is "index-all.html" and it is
 * generated in current or the destination directory.
 *
 * @see java.lang.Character
 * @author Atul M Dambalkar
 */
public class SingleIndexWriter extends AbstractIndexWriter {

    /**
     * Construct the SingleIndexWriter with filename "index-all.html" and the 
     * {@link IndexBuilder}
     * 
     * @param filename     Name of the index file to be generated.
     * @param indexbuilder Unicode based Index from {@link IndexBuilder}
     */
    public SingleIndexWriter(String filename, 
                             IndexBuilder indexbuilder) throws IOException {
        super(filename, indexbuilder);
    }

    /**
     * Generate single index file, for all Unicode characters.
     * 
     * @param indexbuilder IndexBuilder built by {@link IndexBuilder}
     */
    public static void generate(IndexBuilder indexbuilder) 
                                throws DocletAbortException {
        SingleIndexWriter indexgen;
        String filename = "index-all.html";
        try {
            indexgen = new SingleIndexWriter(filename, indexbuilder);
            indexgen.generateIndexFile();
            indexgen.close();
        } catch (IOException exc) {
 Standard.configuration().standardmessage.error("doclet.exception_encountered",
                                                 exc.toString(), filename);
            throw new DocletAbortException();
        }
    }

    /**
     * Generate the contents of each index file, with Header, Footer, 
     * Member Field, Method and Constructor Description.
     */
    protected void generateIndexFile() throws IOException {
        printHeader(getText("doclet.Window_Single_Index",
                            Standard.configuration().windowtitle));

        
        navLinks(true);
        printLinksForIndexes();
        
        hr();
    
        for (int i = 0; i < indexbuilder.elements().length; i++) {
            Character unicode = (Character)((indexbuilder.elements())[i]);
            generateContents(unicode, indexbuilder.getMemberList(unicode));
        }

        printLinksForIndexes();
        navLinks(false);
        
        printBottom(); 
        printBodyHtmlEnd();
    }

    /**
     * Print Links for all the Index Files per unicode character.
     */
    protected void printLinksForIndexes() {
        for (int i = 0; i < indexbuilder.elements().length; i++) {
            String unicode = (indexbuilder.elements())[i].toString();
            printHyperLink("#_" + unicode + "_", unicode);
            print(' ');
        }
    }
}
