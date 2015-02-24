// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.core;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.net.URL;
import java.util.jar.JarInputStream;
import java.util.zip.ZipEntry;


public class WebstartMain {

    private static final int BUFFER_SIZE = 4096;


    private static void delete(File f) {
        if(f.isDirectory()) {
            for(File c : f.listFiles()) {
                delete(c);
            }
        }
        f.delete();
    } 


    public static File setupExamples() {
        try {
            URL examplesURL = WebstartMain.class.getResource("/examples.jar");	
            if(examplesURL == null) {
                throw new IOException("Missing examples.jar in resources");
            }

            File tempDir = createTempDirectory();
            System.out.println(tempDir);

            JarInputStream zis = new JarInputStream(examplesURL.openStream());

            try {
                byte[] buffer = new byte[BUFFER_SIZE];

                for(ZipEntry zipEntry = zis.getNextEntry(); 
                        zipEntry != null;
                        zipEntry = zis.getNextEntry()) {


                    String entryName = zipEntry.getName();
                    File outFile = new File(tempDir, entryName);

                    if(zipEntry.isDirectory()) {

                        boolean mkdirSuccess = outFile.mkdir();
                        if(!mkdirSuccess) {
                            throw new IOException("Cannot create directory " + outFile);
                        }

                    } else {

                        FileOutputStream fos = new FileOutputStream(outFile);

                        try {
                            int n;
                            while ((n = zis.read(buffer, 0, BUFFER_SIZE)) > -1) {
                                fos.write(buffer, 0, n);
                            }
                        } finally {
                            fos.close();
                        }
                        zis.closeEntry();
                    }
                }
            } finally {
                zis.close();
            }
            return tempDir;
        } catch(IOException e) {
            e.printStackTrace();
            return null;
        } 
    }


    private static File createTempDirectory() throws IOException {
        final File tempDir = File.createTempFile("keyheap-examples-", null);
        tempDir.delete();
        if(!tempDir.mkdir()) {
            return null;
        }
        Runtime.getRuntime().addShutdownHook(new Thread() {
            public void run() {
                delete(tempDir);
            }
        });
        return tempDir;
    }


    public static void main(String[] args) {
        File examplesDir = setupExamples();

        if(examplesDir != null) {
            String[] newArgs = new String[args.length + 2];
            System.arraycopy(args, 0, newArgs, 0, args.length);
            newArgs[args.length] = "--examples";
            newArgs[args.length + 1] = examplesDir.getAbsolutePath();
            args = newArgs;
        }

        Main.main(args);
    }
}