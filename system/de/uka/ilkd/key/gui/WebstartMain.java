// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

// Adapted from keymaera, original author jdq


package de.uka.ilkd.key.gui;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;

import de.uka.ilkd.key.gui.Main;


public class WebstartMain {

    public static void main(String[] args) {
	InputStream resourceAsStream 
		= WebstartMain.class
		              .getResourceAsStream("/examples/heap/test.key");
	
	if(resourceAsStream != null) {
	    try {
		File tempFile = File.createTempFile("test", ".key");
		tempFile.deleteOnExit();
		System.out.println(tempFile.getCanonicalPath());
		FileOutputStream fileOutputStream = new FileOutputStream(tempFile);
		int i;
		while ((i = resourceAsStream.read()) != -1) {
		    fileOutputStream.write((char) i);
		}
		resourceAsStream.close();
		fileOutputStream.close();
		
		String[] newArgs = new String[args.length + 1];
		System.arraycopy(args, 0, newArgs, 0, args.length);
		newArgs[args.length] = tempFile.getCanonicalPath();
		args = newArgs;
	    } catch (IOException e) {
		assert false;
	    }
	}
	Main.main(args);
    }
}
