// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/**
 * KeYResourceManager controls the access to the properties
 * and resources used in the KeY system.
 * Use the static method getManager to get the unique instance.
 */

package de.uka.ilkd.key.util;

import java.io.*;
import java.net.URL;

import javax.swing.ImageIcon;

public class KeYResourceManager {

    /** the unique instance */
    private static final KeYResourceManager instance 
	= new KeYResourceManager();

    private String version = null;
    private String sha1 = null;

    private KeYResourceManager() {
    }

    /**
     * Return an instance of the ResourceManager
     */
    public static KeYResourceManager getManager() {
	return instance;
    }


    /**
     * reads a version string or returns "x.z.y" in case of failures
     */
    private String readVersionString(URL url) {
	String result = "";
	if (url != null) {
	    try {
		final InputStream io = 
                    new BufferedInputStream(url.openStream()); 
		int c;
		while ((c=io.read()) !=-1) {
		    result += (char)c;
		}
	    } catch (IOException ioe) {
		// who cares it is just a version number
		result = "x.z.y";
	    }
	} else {
	    result = "x.z.y";
	}
	return result.trim();
    }

    /**
     * returns the SHA 1 git code from which this version has been 
     * derived
     * @return returns the SHA1 hash uniquely identifying the version
     */
    public String getSHA1() {
	if (sha1 != null) {
	    return sha1;
	}
	sha1 = 
	    readVersionString(getResourceFile(this, "sha1")); 

	return sha1;
    }

    /**
     * returns a readable customizable version number    
     * @return a readable version number  
     */
    public String getVersion() {      
	if (version != null) {
	    return version;
	}
	version = 
	    readVersionString(getResourceFile(this, "version")); 

	return version;
    }

    /**
     * Creates an icon from an image contained in a resource.
     * The resource is fist search using the package name of the calling Object
     * and if it is not found there the packagename of its superclass is used
     * recusrivly.
     * @param o the Object reference to the calling object
     * @param filename String the name of the file to search (only relative
     * pathname to the path of the calling class)
     * @return the newly created image
     */
    public ImageIcon createImageIcon(Object o, String filename) {
	return createImageIcon(o.getClass(), filename);
    }

    /**
     * Creates an icon from an image contained in a resource.
     * The resource is fist search using the package name of the given class
     * and if the resource is not found the packagename of its superclass is used
     * recursivly.
     * @param cl the Class the resource is looked for
     * @param filename String the name of the file to search  (only relative
     * pathname to the path of the calling class)
     * @return the newly created image
     */
    public ImageIcon createImageIcon(Class cl, String filename) {
	URL iconURL = cl.getResource(filename);
	Debug.out("Load Resource:" + filename + " of class "+cl);
	if (iconURL == null && cl.getSuperclass() != null) {
	    return createImageIcon(cl.getSuperclass(),
				   filename);
	} else if (iconURL == null && cl.getSuperclass() == null) {
	    // error message Resource not found
	    System.out.println("No image resource "+ filename + " found");
	    return null;
	} else { 
	    Debug.out("Done.");
	    return new ImageIcon(iconURL); 
	}
    }

    /**
     * Copies the specified resource to targetLocation if such a file
     * does not exist yet.
     * The created file is removed automatically after finishing JAVA.
     * @param o an Object the directory from where <code>resourcename</code>
     * is copied is determined by looking on the package where <code>o.getClass()</code>
     * is declared  
     * @param resourcename String the name of the file to search  (only relative
     * pathname to the path of the calling class)
     * @param targetLocation target for copying
     * @return true if resource was copied 
     */
    public  boolean copyIfNotExists(Object o, String resourcename, 
				    String targetLocation) {
	return copyIfNotExists(o.getClass(),resourcename,targetLocation);
    }

    public boolean copyIfNotExists(Class cl, String resourcename, 
				   String targetLocation) {
	URL resourceURL = cl.getResource(resourcename);

        Debug.out("Load Resource:"+resourcename+" of class "+cl);
	
        if (resourceURL == null && cl.getSuperclass() != null) {
	    return  copyIfNotExists(cl.getSuperclass(),
				    resourcename,
				    targetLocation);
	} else if (resourceURL == null && cl.getSuperclass() == null) {
	    // error message Resource not found
	    System.out.println("No resource "+ resourcename + " found");
	    return false;
	} 
        
	// copying the resource to the target if targetfile 
	// does not exist yet
	boolean result = false;
	try{
	    File targetFile = new File(targetLocation);
	    if (!targetFile.exists()){
		result = true;
		if (targetFile.getParentFile() != null) {
		    targetFile.getParentFile().mkdirs();
		}
		targetFile.createNewFile();	    
		targetFile.deleteOnExit();
		
		InputStream sourceStream = resourceURL.openStream();
		FileOutputStream targetStream = 
		    new FileOutputStream (targetFile);  
		
		int copyItem;
		copyItem = sourceStream.read();
		while (copyItem > -1){
		    targetStream.write(copyItem);
		    copyItem = sourceStream.read();
		}
		sourceStream.close();
		targetStream.close();
	    }
	} catch(Exception e) {
	    System.err.println("KeYError: " + e);
	    return false;
	}	
	return result;
    }


    /** loads a resource and returns its URL 
     * @param cl the Class used to determine the resource 
     * @param resourcename the String that contains the name of the resource
     * @return the URL of the resource
     */
    public URL getResourceFile(Class cl, String resourcename) {
        URL resourceURL = cl.getResource(resourcename);
	if (resourceURL == null && cl.getSuperclass() != null) {
	    return getResourceFile(cl.getSuperclass(), resourcename);
	} else if (resourceURL == null && cl.getSuperclass() == null) {
	    return null;
	}
	return resourceURL;	
    }

    /** loads a resource and returns its URL 
     * @param o the Object used to determine the resource 
     * @param resourcename the String that contains the name of the resource
     * @return the URL of the resource
     */
    public URL getResourceFile(Object o, String resourcename) {
	return getResourceFile(o.getClass(), resourcename);
    }
}
