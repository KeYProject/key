// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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
import java.util.Enumeration;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

import de.uka.ilkd.key.gui.Main;


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

			InputStream inputStream = jarFile.getInputStream(entry);
			FileOutputStream outputStream 
				= new FileOutputStream(localFile);
			int i;
			while ((i = inputStream.read()) != -1) {
			    outputStream.write((char) i);
			}
			inputStream.close();
			outputStream.close();
		    }
		}
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
