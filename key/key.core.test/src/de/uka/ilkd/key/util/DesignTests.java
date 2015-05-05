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

import org.junit.Assert;
import org.junit.Before;
import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.logic.Term;


/** 
 * This class tests, if design principles have been hurt. Therefore it
 * makes use of reflection.
 */
public class DesignTests extends TestCase {

    private static final File binaryPath;
          
    static {
       File projectRoot = IOUtil.getClassLocation(Term.class);
       if ("org.key_project.core".equals(projectRoot.getName())) {
          projectRoot = new File(projectRoot, "bin");
       } else if (projectRoot.isFile()) {
          projectRoot = new File(projectRoot.getParentFile().getParentFile().getParentFile(), "key.core" + File.separator + "bin");
       }
       
       binaryPath = new File(projectRoot, "de"+File.separator+"uka"+File.separator+"ilkd"+File.separator+"key");
    }
    
    private static final FileFilter FILTER = new FileFilter() {
        public boolean accept(File fileName) {
            final String absolutePath = fileName.getAbsolutePath();
            return absolutePath.endsWith(".class");
        }
        };

    private Class<?>[] allClasses;

    private String message = "";

    /**
     * Creates an instance used to test if design principles have been
     * hurt.
     */
    public DesignTests() {
    }

    @Before
    public void setUp() {
      allClasses = getAllClasses(binaryPath);
	   Assert.assertTrue("No classes found in and below " + binaryPath, allClasses.length >= 1);
    }

    /** 
     * collects all found in the given directory
     * @param directory a File denoting the directory where to look for
     * the classes
     * @return array of found class files
     */
    private static Class<?>[] getClasses(File directory) {
	System.out.print(".");
	File[] classFiles = directory.listFiles(FILTER);	

	Class<?>[] classes = new Class
	    [(classFiles == null) ? 0 : classFiles.length];
	for (int i = 0; i<classes.length; i++) {
	    String absoluteName = classFiles[i].getAbsolutePath();
	    String className = absoluteName.substring
		(absoluteName.indexOf("de"+File.separatorChar)).replace(File.separatorChar, '.');
	    className = className.substring(0, className.indexOf(".class"));
	    
	    try {
		    classes[i] = Term.class.getClassLoader().loadClass(className);
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
    private static void copyToList(Class<?>[] source, LinkedList<Class<?>> target) {
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
    public static Class<?>[] getAllClasses(File topDir) {
       LinkedList<Class<?>> result = new LinkedList<Class<?>>();
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
    private String printBadClasses(LinkedList<Class<?>> badClasses) {
	StringBuilder sb = new StringBuilder();
	Iterator<Class<?>> it = badClasses.iterator();	
	if (it.hasNext()) {
	    sb.append("Bad classes:");
	    while (it.hasNext()) {	    
		sb.append("\n"+it.next());
	    }	
	}
	return sb.toString();
   }

    /**
     * subclass of Term must be private or package private
     */
    public void testTermSubclassVisibility() {
	LinkedList<Class<?>> badClasses = new LinkedList<Class<?>>();
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
        LinkedList<Class<?>> badClasses = new LinkedList<Class<?>>();
        for (int i = 0; i<allClasses.length; i++) {
            if (de.uka.ilkd.key.rule.Rule.class.isAssignableFrom(allClasses[i]) ||
                    allClasses[i].getPackage().getName().contains("key.rule") ||
                    allClasses[i].getPackage().getName().contains("key.logic")  ||
                    allClasses[i].getPackage().getName().contains("key.proof") ||
                    allClasses[i].getPackage().getName().contains("de.uka.ilkd.key.smt.counterexample") ||
                    allClasses[i].getPackage().getName().contains("de.uka.ilkd.key.smt.testgen") ||
                    allClasses[i].getPackage().getName().contains("key.java") ||   
                    allClasses[i].getPackage().getName().contains("key.core") ||   
                    allClasses[i].getPackage().getName().contains("key.settings") ||   
                    allClasses[i].getPackage().getName().contains("key.strategy")   
                    ) {
                
                // exclude KeYMediator for the moment (contains some workarounds)
                if (allClasses[i].getName().contains("KeYMediator")) continue;
                
                for (Field f : allClasses[i].getDeclaredFields()) {
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
            message = "No GUI is allowed in the packages and there sub packages";
	        message += printBadClasses(badClasses);
        }

	    assertTrue(message, badClasses.size() == 0);
    }
    
    private boolean implementsEquals(Class<?> cl) {
        try {
            cl.getMethod("equals", Object.class);
        } catch (NoSuchMethodException e) {
            return false; // class does not override equals()
        } catch (SecurityException e) {
            System.err.println("hashCode test skipped for type "+cl);
        }
        return true;
    }
    
    private boolean implementsHashCode(Class<?> cl) {
        try {
            cl.getMethod("hashCode");
        } catch (NoSuchMethodException e) {
            // class does not override hashCode
            return false;
        } catch (SecurityException e) {
            System.err.println("hashCode test skipped for type "+cl);
        }
        return true;
    }

    /**
     * Tests that if <code>equals()</code> is overriden,
     * <code>hashCode()</code> is also overriden.
     */
    public void testHashCodeImplemented() {
        LinkedList<Class<?>> badClasses = new LinkedList<Class<?>>();
        for (int i = 0; i<allClasses.length; i++) {
            Class<?> clazz = allClasses[i];
            if (implementsEquals(clazz) && !implementsHashCode(clazz)) {
                badClasses.add(clazz);
            }
        }
        if (badClasses.size()>0) {
            message = "Classes that override equals() must also override hashCode().\n";
            message += printBadClasses(badClasses);
        }

        assertTrue(message, badClasses.size() == 0);
    }




    public void runTests() {
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
                    System.err.println("Test failed: "+meth[i]);
                    e.printStackTrace();
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