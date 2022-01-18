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

import de.uka.ilkd.key.logic.Term;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import org.key_project.util.java.IOUtil;

import java.io.File;
import java.io.FileFilter;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;


/**
 * This class tests, if design principles have been hurt. Therefore it
 * makes use of reflection.
 */
public class DesignTests {

    private static final File binaryPath;

    static {
        File projectRoot = IOUtil.getClassLocation(Term.class);
        if ("org.key_project.core".equals(projectRoot.getName())) {
            projectRoot = new File(projectRoot, "bin");
        } else if (projectRoot.isFile()) {
            projectRoot = new File(projectRoot.getParentFile().getParentFile().getParentFile(), "key.core" + File.separator + "bin");
        }

        binaryPath = new File(projectRoot, "de" + File.separator + "uka" + File.separator + "ilkd" + File.separator + "key");
    }

    private static final FileFilter FILTER = fileName -> {
        final String absolutePath = fileName.getAbsolutePath();
        return absolutePath.endsWith(".class");
    };

    private Class<?>[] allClasses;

    private String message = "";

    /**
     * Creates an instance used to test if design principles have been
     * hurt.
     */
    public DesignTests() {
    }

    @BeforeEach
    public void setUp() {
        allClasses = getAllClasses(binaryPath);
        Assertions.assertTrue(allClasses.length >= 1, "No classes found in and below " + binaryPath);
    }

    /**
     * collects all found in the given directory
     *
     * @param directory a File denoting the directory where to look for
     *                  the classes
     * @return array of found class files
     */
    private static Class<?>[] getClasses(File directory) {
        System.out.print(".");
        File[] classFiles = directory.listFiles(FILTER);

        Class<?>[] classes = new Class
                [(classFiles == null) ? 0 : classFiles.length];
        for (int i = 0; i < classes.length; i++) {
            String absoluteName = classFiles[i].getAbsolutePath();
            String className = absoluteName.substring
                    (absoluteName.indexOf("de" + File.separatorChar)).replace(File.separatorChar, '.');
            className = className.substring(0, className.indexOf(".class"));

            try {
                classes[i] = Term.class.getClassLoader().loadClass(className);
            } catch (ClassNotFoundException cnfe) {
                System.err.println("That's weiry. Cannot find class " +
                        className + "\n" + cnfe);
            } catch (NoClassDefFoundError ncdfe) {
                System.err.println(className + " skipped. " +
                        "Please check your classpath.");
            }
        }

        return classes;
    }

    /**
     * adds all elements of <code>source</code> to <code>target</code>
     *
     * @param source the array whose elements have to inserted
     * @param target the LinkedList where to insert the elements of the
     *               source
     */
    private static void copyToList(Class<?>[] source, LinkedList<Class<?>> target) {
        Collections.addAll(target, source);
    }

    /**
     * iterates through the directory structure starting at
     * <code>topDir</code> and collects all found
     * classes.
     *
     * @param topDir File giving the directory where to start the
     *               iteration
     * @return all found classes including the ones in
     * <code>topDir</code>
     */
    public static Class<?>[] getAllClasses(File topDir) {
        LinkedList<Class<?>> result = new LinkedList<>();
        copyToList(getClasses(topDir), result);

        File[] subDirectories = topDir.listFiles
                (File::isDirectory);
        if (subDirectories == null) {
            return new Class[0];
        } else {
            for (File subDirectory : subDirectories) {
                copyToList(getAllClasses(subDirectory), result);
            }
            return (Class<?>[]) result.toArray(new Class[0]);
        }
    }

    /**
     * prints an enumeration of of those classes that hurt a design principle
     */
    private String printBadClasses(LinkedList<Class<?>> badClasses) {
        StringBuilder sb = new StringBuilder();
        Iterator<Class<?>> it = badClasses.iterator();
        if (it.hasNext()) {
            sb.append("Bad classes:");
            while (it.hasNext()) {
                sb.append("\n").append(it.next());
            }
        }
        return sb.toString();
    }

    /**
     * subclass of Term must be private or package private
     */
    @Disabled("weigl: stupid test")
    @Test
    public void xtestTermSubclassVisibility() {
        LinkedList<Class<?>> badClasses = new LinkedList<>();
        for (Class<?> allClass : allClasses) {
            if (allClass != Term.class &&
                    (Term.class).isAssignableFrom(allClass)) {
                int mods = allClass.getModifiers();
                if (Modifier.isProtected(mods) ||
                        Modifier.isPublic(mods)) {
                    badClasses.add(allClass);
                }
            }
        }
        if (badClasses.size() > 0) {
            message = "Visibility of subclasses of Term  ";
            message += "must be package private or private.\n";
            message += printBadClasses(badClasses);
        }
        Assertions.assertEquals(0, badClasses.size(), message);
    }

    /**
     * does not test if GUI is used within methods
     */
    @Test
    public void testGuiSep() {
        LinkedList<Class<?>> badClasses = new LinkedList<>();
        for (Class<?> allClass : allClasses) {
            if (de.uka.ilkd.key.rule.Rule.class.isAssignableFrom(allClass) ||
                    allClass.getPackage().getName().contains("key.rule") ||
                    allClass.getPackage().getName().contains("key.logic") ||
                    allClass.getPackage().getName().contains("key.proof") ||
                    allClass.getPackage().getName().contains("de.uka.ilkd.key.smt.counterexample") ||
                    allClass.getPackage().getName().contains("de.uka.ilkd.key.smt.testgen") ||
                    allClass.getPackage().getName().contains("key.java") ||
                    allClass.getPackage().getName().contains("key.core") ||
                    allClass.getPackage().getName().contains("key.settings") ||
                    allClass.getPackage().getName().contains("key.strategy")
            ) {

                // exclude KeYMediator for the moment (contains some workarounds)
                if (allClass.getName().contains("KeYMediator")) continue;

                for (Field f : allClass.getDeclaredFields()) {
                    if (java.awt.Component.class.isAssignableFrom(f.getType())) { //|| pkgname.contains("key.gui")) { as long as the mediator and settings are in the GUI
                        System.out.println("Illegal GUI reference at field " + f.getName() + " declared in class " + allClass.getName());
                        badClasses.add(allClass);
                    }
                }

                for (Method m : allClass.getDeclaredMethods()) {
                    if (java.awt.Component.class.isAssignableFrom(m.getReturnType())) {
                        System.out.println("Illegal GUI reference as return type of " + m.getName() + " declared in class " + allClass.getName());
                        badClasses.add(allClass);
                    }
                    for (Class<?> t : m.getParameterTypes())
                        if (java.awt.Component.class.isAssignableFrom(t)) {
                            System.out.println("Illegal GUI reference as parameter type of " + m.getName() + " declared in class " + allClass.getName());
                            badClasses.add(allClass);
                        }
                }
            }
        }
        if (badClasses.size() > 0) {
            message = "No GUI is allowed in the packages and there sub packages";
            message += printBadClasses(badClasses);
        }

        Assertions.assertEquals(0, badClasses.size(), message);
    }

    private boolean implementsEquals(Class<?> cl) {
        try {
            cl.getMethod("equals", Object.class);
        } catch (NoSuchMethodException e) {
            return false; // class does not override equals()
        } catch (SecurityException e) {
            System.err.println("hashCode test skipped for type " + cl);
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
            System.err.println("hashCode test skipped for type " + cl);
        }
        return true;
    }

    /**
     * Tests that if <code>equals()</code> is overriden,
     * <code>hashCode()</code> is also overriden.
     */
    @Test
    public void testHashCodeImplemented() {
        LinkedList<Class<?>> badClasses = new LinkedList<>();
        for (Class<?> clazz : allClasses) {
            if (implementsEquals(clazz) && !implementsHashCode(clazz)) {
                badClasses.add(clazz);
            }
        }
        if (badClasses.size() > 0) {
            message = "Classes that override equals() must also override hashCode().\n";
            message += printBadClasses(badClasses);
        }

        Assertions.assertEquals(0, badClasses.size(), message);
    }


    public void runTests() {
        Method[] meth = getClass().getMethods();
        System.out.println("[Design Conformance Tests]");
        System.out.println("[Collecting classes. Please wait...]");
        allClasses = getAllClasses(binaryPath);
        System.out.println("\n[Testing " + allClasses.length + " classes.]");
        int failures = 0;
        int testcases = 0;
        for (Method method : meth) {
            if (method.getName().startsWith("test")) {
                try {
                    testcases++;
                    message = ".";
                    method.invoke(this, (Object[]) null);
                    System.out.print(message);
                } catch (Exception e) {
                    System.err.println("Test failed: " + method);
                    e.printStackTrace();
                    failures++;
                }
            }
        }
        System.out.println("\n[Design tests finished. (" + (testcases - failures) +
                "/" + testcases + ") tests passed.]");
        if (failures > 0) {
            System.exit(1);
        }
    }

    public static void main(String[] args) {
        DesignTests tests = new DesignTests();
        tests.runTests();
    }
}