/*
 * @(#)PackageListWriter.java	1.5 00/02/02
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
 * Write out the package index.
 *
 * @see com.sun.javadoc.PackageDoc
 * @see com.sun.tools.doclets.HtmlDocWriter
 * @author Atul M Dambalkar 
 */
public class PackageListWriter extends HtmlStandardWriter {

    /**
     * Constructor.
     */
    public PackageListWriter(String filename) throws IOException {
        super(filename);
    }

    /**
     * Generate the package index.
     *
     * @param root the root of the doc tree.
     */
    public static void generate(RootDoc root) throws DocletAbortException {
        PackageListWriter packgen;
        String filename = "package-list";
        try {
            packgen = new PackageListWriter(filename);
            packgen.generatePackageListFile(root);
            packgen.close();
        } catch (IOException exc) {
 Standard.configuration().standardmessage.error("doclet.exception_encountered", 
                                                 exc.toString(), filename);
            throw new DocletAbortException();
        }
    }

    protected void generatePackageListFile(RootDoc root) {
        PackageDoc[] packages = Standard.configuration().packages;
        for (int i = 0; i < packages.length; i++) {
            println(packages[i].name());
        } 
    }
}



