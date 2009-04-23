// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.util;

import java.io.File;
import java.io.FileFilter;
import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.Iterator;
import java.util.LinkedList;

/** 
 * This class tests, if design principles have been hurt. Therefore it
 * makes use of reflection.
 */

public class DesignTests {

    private static final File binaryPath = 
	new File(System.getProperty("key.home")+File.separator+"system"+
	File.separator+"binary");

    private Class[] allClasses;

    private String message = "";

    /**
     * Creates an instance used to test if design principles have been
     * hurt.
     */
    public DesignTests() {
    }

    /** 
     * collects all found in the given directory
     * @param directory a File denoting the directory where to look for
     * the classes
     * @return array of found class files
     */
    private static Class[] getClasses(File directory) {
	System.out.print(".");
	File[] classFiles = directory.listFiles(new FileFilter() {
		public boolean accept(File fileName) {
		    return fileName.getAbsolutePath().indexOf("de/") != -1 &&
			fileName.getAbsolutePath().endsWith(".class");
		}
	    });	

	Class[] classes = new Class
	    [(classFiles == null) ? 0 : classFiles.length];
	for (int i = 0; i<classes.length; i++) {
	    String absoluteName = classFiles[i].getAbsolutePath();
	    String className = absoluteName.substring
		(absoluteName.indexOf("de/")).replace(File.separatorChar, '.');
	    className = className.substring(0, className.indexOf(".class"));
	    
	    try {
		    classes[i] = ClassLoader.getSystemClassLoader().
			loadClass(className);
	    } catch (ClassNotFoundException cnfe) {
		System.err.println("That's weiry. Cannot find class " + 
				   className+"\n"+cnfe);
	    } catch (NoClassDefFoundError ncdfe) {
	        System.err.println(className +" skipped. " +
                                "Please check your classpath.");
            }
	}

	return classes;
    }

    /**
     * adds all elements of <code>source</code> to <code>target</code>
     * @param source the array whose elements have to inserted
     * @param target the LinkedList where to insert the elements of the
     * source
     */
    private static void copyToList(Object[] source, LinkedList target) {
	for (int i = 0; i<source.length; i++) {
	    target.add(source[i]);
	}
    }
    
    /** 
     * iterates through the directory structure starting at
     * <code>topDir</code> and collects all found
     * classes.
     * @param topDir File giving the directory where to start the
     * iteration 
     * @return all found classes including the ones in
     * <code>topDir</code>
     */
    public static Class[] getAllClasses(File topDir) {
	LinkedList result = new LinkedList();
	copyToList(getClasses(topDir), result);	    

	File[] subDirectories = topDir.listFiles
	(new FileFilter() {
		public boolean accept(File fileName) {
		    return fileName.isDirectory();
		}
	    });
	if (subDirectories == null) {
	    return new Class[0];
	} else {
	    for (int i = 0; i<subDirectories.length; i++) {
		copyToList(getAllClasses(subDirectories[i]), result);
	    }
	    return (Class[])result.toArray(new Class[result.size()]);
	}
    }

    /** prints an enumeration of of those classes that hurt a design principle */
    private void printBadClasses(LinkedList badClasses) {
	Iterator it = badClasses.iterator();	
	if (it.hasNext()) {
	    System.out.println("Bad classes:");
	    while (it.hasNext()) {	    
		System.out.println("\t"+it.next());
	    }	
	}
    }

    /**
     * some operator classes are allowed to have greater visibility 
     */
    private boolean exception(Class cl) {
	return 
	    (cl == de.uka.ilkd.key.logic.op.Junctor.class); // ASMKEY extends Junctor
    }

    /**
     * subclass of Op should have at most package private constructors
     * (exception: metaop)
     */
    public LinkedList testConstructorInOpSubclasses() {
	LinkedList badClasses = new LinkedList();
	for (int i = 0; i<allClasses.length; i++) {
 	    if (allClasses[i] != de.uka.ilkd.key.logic.op.Op.class &&
		(de.uka.ilkd.key.logic.op.Op.class).
		isAssignableFrom(allClasses[i]) &&
		!(de.uka.ilkd.key.logic.op.
		  AbstractMetaOperator.class).isAssignableFrom(allClasses[i])) {
 		Constructor[] cons = allClasses[i].getConstructors();
 		for (int j = 0; j<cons.length; j++) {
 		    int mods = cons[j].getModifiers();
 		    if ((Modifier.isProtected(mods) && !exception(allClasses[i])) ||
 			Modifier.isPublic(mods)) {
 			badClasses.add(allClasses[i]);
 		    }
 		}
 	    }
	}
	if (badClasses.size()>0) {
	    message = "Constructors of subclasses of 'Op'  ";
	    message += "must have package private or private";
	    message += "(except MetaOperators).\n";	    
	}
	return badClasses;
    }

    /**
     * subclass of Term must be private or package private
     */
    public LinkedList testTermSubclassVisibility() {
	LinkedList badClasses = new LinkedList();
	for (int i = 0; i<allClasses.length; i++) {
 	    if (allClasses[i] != de.uka.ilkd.key.logic.Term.class &&
		(de.uka.ilkd.key.logic.Term.class).
		isAssignableFrom(allClasses[i])) {
		int mods = allClasses[i].getModifiers();
		if (Modifier.isProtected(mods) ||
		    Modifier.isPublic(mods)) {
		    badClasses.add(allClasses[i]);
 		}
 	    }
	}
	if (badClasses.size()>0) {
	    message = "Visibility of subclasses of Term  ";
	    message += "must be package private or private.\n";
	}
	return badClasses;
    }



    public void runTests() {
	LinkedList badClasses; 	
	Method[] meth = getClass().getMethods();
	System.out.println("[Design Conformance Tests]");	
	System.out.println("[Collecting classes. Please wait...]");
	allClasses = getAllClasses(binaryPath);
	System.out.println("\n[Testing "+allClasses.length+" classes.]");	
	int failures = 0;
	int testcases = 0;
	for (int i = 0; i<meth.length; i++) {
	    if (meth[i].getName().startsWith("test")) {
		try {
		    message = ".";
		    badClasses = (LinkedList)meth[i].invoke(this, null);
		    System.out.print(message);
		    testcases++;
		    failures += badClasses.size() > 0 ? 1 : 0;
		    printBadClasses(badClasses);
		} catch (Exception e) {
		    System.err.println("Could not invoke method "+meth);
		}
	    }
	}	
	System.out.println("\n[Tests finished. ("+(testcases-failures)+
			   "/"+testcases+") tests passed.]");
    }
    
    public static void main(String[] args) {
	DesignTests tests = new DesignTests();	
	tests.runTests();
    }


}
