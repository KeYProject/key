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

package de.uka.ilkd.key.util;

import java.io.File;
import java.io.FileFilter;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.Iterator;
import java.util.LinkedList;
import junit.framework.TestCase;


/** 
 * This class tests, if design principles have been hurt. Therefore it
 * makes use of reflection.
 */
public class DesignTests extends TestCase {

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

    public void setUp() {
	allClasses = getAllClasses(binaryPath);
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
		(absoluteName.indexOf("de"+File.separatorChar)).replace(File.separatorChar, '.');
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
    private String printBadClasses(LinkedList badClasses) {
	StringBuilder sb = new StringBuilder();
	Iterator it = badClasses.iterator();	
	if (it.hasNext()) {
	    sb.append("Bad classes:");
	    while (it.hasNext()) {	    
		sb.append("\t"+it.next());
	    }	
	}
	return sb.toString();
   }

    /**
     * subclass of Term must be private or package private
     */
    public void testTermSubclassVisibility() {
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
	if ( badClasses.size() > 0 ) {
	    message = "Visibility of subclasses of Term  ";
	    message += "must be package private or private.\n";
	    message += printBadClasses(badClasses);
	}
	assertTrue(message, badClasses.size() == 0);
    }

    /** does not test if GUI is used within methods */
    public void testGuiSep() {
        LinkedList badClasses = new LinkedList();
        for (int i = 0; i<allClasses.length; i++) {
            if (de.uka.ilkd.key.rule.Rule.class.isAssignableFrom(allClasses[i]) ||
                    allClasses[i].getPackage().getName().contains("key.rule") ||
                    allClasses[i].getPackage().getName().contains("key.logic")  ||
                    allClasses[i].getPackage().getName().contains("key.proof") ||
                    allClasses[i].getPackage().getName().contains("key.java") ||   
                    allClasses[i].getPackage().getName().contains("key.strategy")   
                    ) {
                for (Field f : allClasses[i].getDeclaredFields()) {
                    Package pkg = f.getType().getPackage();
                    String pkgname = pkg != null ? pkg.getName() : "";
                    if (java.awt.Component.class.isAssignableFrom(f.getType())) { //|| pkgname.contains("key.gui")) { as long as the mediator and settings are in the GUI
                        System.out.println("Illegal GUI reference at field " + f.getName() + " declared in class " + allClasses[i].getName());
                        badClasses.add(allClasses[i]);
                    }                
                }
                                
                for (Method m : allClasses[i].getDeclaredMethods()) {
                    if (java.awt.Component.class.isAssignableFrom(m.getReturnType())) {
                        System.out.println("Illegal GUI reference as return type of " + m.getName() + " declared in class " + allClasses[i].getName());
                        badClasses.add(allClasses[i]);
                    }
                    for (Class<?> t : m.getParameterTypes())
                    if (java.awt.Component.class.isAssignableFrom(t)) {
                        System.out.println("Illegal GUI reference as parameter type of " + m.getName() + " declared in class " + allClasses[i].getName());
                        badClasses.add(allClasses[i]);
                    }                    
                }                
            }
        }
        if (badClasses.size()>0) {
            message = "No GUI is allowd in the packages and there sub packages";
	    message += printBadClasses(badClasses);
        }

	assertTrue(message, badClasses.size() == 0);
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
		    testcases++;
		    message = ".";
		    meth[i].invoke(this, (Object[])null);
		    System.out.print(message);
		} catch (Exception e) {
		    e.printStackTrace();
		    System.err.println("Could not invoke method "+meth[i]);
                    failures ++;
		}
	    }
	}	
	System.out.println("\n[Design tests finished. ("+(testcases-failures)+
			   "/"+testcases+") tests passed.]");
	if (failures > 0) {
	    System.exit(1);	    
	}
    }
    
    public static void main(String[] args) {
	DesignTests tests = new DesignTests();	
	tests.runTests();
    }
}