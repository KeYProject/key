// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.util;


import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;


/** 
 * The Service class contains a static method to load a class and a
 * create an instance specified by an identifier. The corresponding
 * class can be specified by a system property or by a service entry
 * in the META-INF directory. 
 */

public final class Service {

    
    /** Search for a class with id and return a new instance. If no
     * class is found, defaultClassName is used instead. */
    public static final Object find(String id, String defaultClassName) {
	// use the system property first
	String systemProperty = System.getProperty(id);
	if (systemProperty != null) {
	    return newInstance(systemProperty);
	}
	
	// try to find services in classpath
	String serviceId = "META-INF/services/" + id;
	InputStream in = ClassLoader.getSystemResourceAsStream(serviceId);
	if (in != null) {
	    try {
		BufferedReader rd = new BufferedReader(new InputStreamReader(in, "UTF-8"));
		String className = rd.readLine();
		rd.close();
		if (className != null && !"".equals(className)) {
		    return newInstance(className);
		}
	    } catch (IOException ioe) {
		throw new RuntimeException("Error: " + ioe);
	    }
	}

	// fall back to default
	return newInstance(defaultClassName);
    }


    /** create and return a new instance of className. */
    private static final Object newInstance(String className) {
	try {
	    Class cl = Class.forName(className);
	    return cl.newInstance();
	} catch (ClassNotFoundException cnfe) {
	    throw new RuntimeException("Service " + className + " not found.");
	} catch (Exception e) {
	    throw new RuntimeException("Service " + className + " could not be instantiated: " + e);
	}
    }


    /** no instances of this class are required. */
    private Service() { }

}
