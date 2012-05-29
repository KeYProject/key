// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import java.io.*;
import java.net.JarURLConnection;
import java.net.URL;
import java.nio.channels.Channel;
import java.nio.channels.Channels;
import java.nio.channels.FileChannel;
import java.nio.channels.ReadableByteChannel;
import java.util.Enumeration;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;


public class WebstartMain {
    
    private static void delete(File f) {
	if(f.isDirectory()) {
	    for(File c : f.listFiles()) {
		delete(c);
	    }
	}
	f.delete();
    } 

        
    private static File setupExamples() {
	try {
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

	    //get jar file
	    URL examplesURL = WebstartMain.class.getResource("/examples/heap/");	
	    JarURLConnection conn 
	    	= (JarURLConnection)examplesURL.openConnection();

            JarFile jarFile = conn.getJarFile();
            try {
                //read relevant entries
                Enumeration<JarEntry> entries = jarFile.entries();
                while(entries.hasMoreElements()) {
                    JarEntry entry = entries.nextElement();
                    if(entry.getName().startsWith("examples/heap/")) {
                        String relativeName 
                        = entry.getName().substring("examples/heap/".length());
                        if(relativeName.length() == 0) {
                            continue;
                        }

                        File localFile 
                        = new File(tempDir.getAbsolutePath(), relativeName);
                        if(entry.isDirectory()) {
                            if(!localFile.mkdir()) {
                                return null;
                            }
                        } else {
                            if(!localFile.createNewFile()) {
                                return null;
                            }
                            ReadableByteChannel inChan = Channels.newChannel(jarFile.getInputStream(entry));
                            FileChannel outChan = new FileOutputStream(localFile).getChannel();
                            try { 
                                outChan.transferFrom(inChan, 0, entry.getSize());
                            } finally {
                                inChan.close();
                                outChan.close();
                            }
                        }   
                    }
                }
            } finally {
                jarFile.close();
            }
	    return tempDir;
	} catch(IOException e) {
	    return null;
	} 
    }
    
    
    public static void main(String[] args) {
	File examplesDir = setupExamples();

	if(examplesDir != null) {
	    String[] newArgs = new String[args.length + 2];
	    System.arraycopy(args, 0, newArgs, 0, args.length);
	    newArgs[args.length] = "EXAMPLES";
	    newArgs[args.length + 1] = examplesDir.getAbsolutePath();
	    args = newArgs;
	}

	Main.main(args);
    }
}
