// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.together.scripts.patternupdate;

import java.io.File;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.net.JarURLConnection;
import java.util.Enumeration;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

import com.togethersoft.openapi.ide.IdeContext;
import com.togethersoft.openapi.ide.message.IdeMessageManagerAccess;
import com.togethersoft.openapi.ide.message.IdeMessageType;

import de.uka.ilkd.key.casetool.together.keydebugclassloader.KeyScript;

/** The intention of this script is to keep the patterns up to date if another
 * version of the KeY jar file is used.  The patterns cannot
 * be accessed if they are inside a jar file so we have to copy them to another
 * place outside the jar file. The position is given by the system property
 * 'key.pattern.path'. Copying the patterns once after the jar file is installed
 * raises the problem that after the jar file is updated the changed or new
 * patterns cannot be used. So we have to check if the installed patterns are up
 * to date or if new ones have been added and if so to copy them.  */

public class PatternUpdate extends KeyScript {
 
    private JarFile jarFile;
    private File patternDirectory;


    /** Reactivate the script */
    public void run1(IdeContext context) {
	autorun1();
    }

    /**
     * Activate the script (cmp. KeyScript)
     */ 
    public void autorun1() { 
        IdeMessageManagerAccess.printMessage
	    (IdeMessageType.INFORMATION, "Patternupdate script: started");
	updatePatterns();
        IdeMessageManagerAccess.printMessage
	    (IdeMessageType.INFORMATION, "Patternupdate script: finished");
    }

    private void updatePatterns() {
	String patternDirProp = System.getProperty("key.pattern.path");
	try {
	    if (patternDirProp != null && !"".equals(patternDirProp)) {
		patternDirectory = new File(patternDirProp);
	    }
	    jarFile = ((JarURLConnection)getClass().
		 getResource("Manifest.mf")
		       .openConnection()).getJarFile();
	} catch (java.io.IOException io) {
	    System.err.println("Error opening jar file.");
	    io.printStackTrace();	    
	    return;
	} catch (ClassCastException cce) {
	    de.uka.ilkd.key.util.Debug.out("No jar file installation.");
	    // no jar file installation
	    return ;
	} 
	copyPatterns();
    }
    
    /** looks through the jar entries and copies the pattern files */
    private void copyPatterns() {
	String dest_prefix = patternDirectory.getAbsolutePath()+"/";
	Enumeration entries = jarFile.entries();
	while (entries.hasMoreElements()) {
	    JarEntry entry = (JarEntry) entries.nextElement();
	    if (entry.getName().startsWith
		("de/uka/ilkd/key/casetool/together/patterns/JAVA/") || 
		entry.getName().startsWith
		("de/uka/ilkd/key/casetool/together/patterns/HelperClasses/")) {
		if (entry.isDirectory()) {
		    try {
			createDir(new File(dest_prefix+
					   entry.getName()));
		    } catch (java.io.IOException e) {
			System.err.println("Cannot create directory "
					   + dest_prefix+entry.getName());
			e.printStackTrace();
		    }
		} else {
		    de.uka.ilkd.key.util.Debug.out
			("Installing new pattern to "+dest_prefix+
			 entry.getName());
		    copyJarEntry(entry, dest_prefix+
				 entry.getName());
		}
	    }	    
	}
    }

    /** creates the directory structure of the given file */
    private void createDir(File dir) 
	throws java.io.IOException{       
	dir.mkdirs();
    }

    /** copies the patterns */
    private void copyJarEntry(JarEntry src, String dest) {
	try {
	    File destFile = new File(dest);
	    // check if file exists and is equal means same time,
	    // same size
	    if (destFile.lastModified() == src.getTime() &&
		destFile.length() == src.getSize()) {		
		return;
	    }
	    // create directory structure if necessary
	    createDir(destFile.getParentFile());
	    // copy the file
	    InputStream srcStream = jarFile.getInputStream(src);	    
	    FileOutputStream fos = new FileOutputStream(destFile);
	    int content = srcStream.read();
	    while (content != -1) {
		fos.write(content);
		content = srcStream.read();
	    }
	    // mark file to avoid unnecssary copying
	    destFile.setLastModified(src.getTime());
	    fos.close();       
	} catch (java.io.IOException io) {
	    System.err.println("Error writing pattern files.");
	    io.printStackTrace();
	}
    }

}
