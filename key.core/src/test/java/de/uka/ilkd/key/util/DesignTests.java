/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;

import de.uka.ilkd.key.logic.Term;

import org.key_project.util.java.IOUtil;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


/**
 * This class tests, if design principles have been hurt. Therefore, it makes use of reflection.
 */
public class DesignTests {

    private static final Path BINARY_PATH;
    private static final Path PROJECT_ROOT;
    private static final Logger LOGGER = LoggerFactory.getLogger(DesignTests.class);

    static {
        File projectRoot = IOUtil.getClassLocation(Term.class);
        if ("org.key_project.core".equals(projectRoot.getName())) {
            projectRoot = new File(projectRoot, "bin");
        } else if (projectRoot.isFile()) {
            projectRoot = new File(projectRoot.getParentFile().getParentFile().getParentFile(),
                "key.core" + File.separator + "bin");
        }

        PROJECT_ROOT = projectRoot.toPath();
        BINARY_PATH = Paths.get(projectRoot.toString(), "de", "uka", "ilkd", "key");
    }

    private ArrayList<Class<?>> allClasses;

    private String message = "";

    /**
     * Creates an instance used to test if design principles have been hurt.
     */
    public DesignTests() {
    }

    @BeforeEach
    public void setUp() {
        allClasses = getAllClasses(BINARY_PATH, PROJECT_ROOT);
        Assertions.assertFalse(allClasses.isEmpty(),
            "No classes found in and below " + BINARY_PATH);
    }

    /**
     * iterates through the directory structure starting at <code>topDir</code> and collects all
     * found classes.
     *
     * @param path File giving the directory where to start the iteration
     */
    public static ArrayList<Class<?>> getAllClasses(Path path, Path root) {
        ArrayList<Class<?>> acc = new ArrayList<>();
        try (var files = Files.walk(path)) {
            files.forEach(child -> {
                var relative = root.relativize(child).toString();
                var index = relative.indexOf(".class");
                if (index == -1) {
                    return;
                }

                var name = relative.toString().substring(0, index).replace(File.separatorChar, '.');

                try {
                    acc.add(Term.class.getClassLoader().loadClass(name));
                } catch (ClassNotFoundException cnfe) {
                    LOGGER.error("That's weird. Cannot find class {} ", name, cnfe);
                } catch (NoClassDefFoundError ncdfe) {
                    LOGGER.error("{} skipped. Please check your classpath.", name, ncdfe);
                }
            });
        } catch (IOException e) {
            Assertions.fail(e);
        }
        return acc;
    }

    /**
     * prints an enumeration of those classes that hurt a design principle
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
     * does not test if GUI is used within methods
     */
    @Disabled("weigl: stupid test")
    @Test
    public void xtestTermSubclassVisibility() {
        LinkedList<Class<?>> badClasses = new LinkedList<>();
        for (Class<?> allClass : allClasses) {
            if (allClass != Term.class && (Term.class).isAssignableFrom(allClass)) {
                int mods = allClass.getModifiers();
                if (Modifier.isProtected(mods) || Modifier.isPublic(mods)) {
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
            if (de.uka.ilkd.key.rule.Rule.class.isAssignableFrom(allClass)
                    || allClass.getPackage().getName().contains("key.rule")
                    || allClass.getPackage().getName().contains("key.logic")
                    || allClass.getPackage().getName().contains("key.proof")
                    || allClass.getPackage().getName()
                            .contains("de.uka.ilkd.key.smt.counterexample")
                    || allClass.getPackage().getName().contains("de.uka.ilkd.key.smt.testgen")
                    || allClass.getPackage().getName().contains("key.java")
                    || allClass.getPackage().getName().contains("key.core")
                    || allClass.getPackage().getName().contains("key.settings")
                    || allClass.getPackage().getName().contains("key.strategy")) {

                // exclude KeYMediator for the moment (contains some workarounds)
                if (allClass.getName().contains("KeYMediator")) {
                    continue;
                }

                for (Field f : allClass.getDeclaredFields()) {
                    if (java.awt.Component.class.isAssignableFrom(f.getType())) {
                        // || pkgname.contains("key.gui")) { as long as the mediator and settings
                        // are in the GUI
                        LOGGER.error("Illegal GUI reference at field {} declared in class {}",
                            f.getName(), allClass.getName());
                        badClasses.add(allClass);
                    }
                }

                for (Method m : allClass.getDeclaredMethods()) {
                    if (java.awt.Component.class.isAssignableFrom(m.getReturnType())) {
                        LOGGER.error(
                            "Illegal GUI reference as return type of {} declared in class {}",
                            m.getName(), allClass.getName());
                    }
                    for (Class<?> t : m.getParameterTypes()) {
                        if (java.awt.Component.class.isAssignableFrom(t)) {
                            LOGGER.error(
                                "Illegal GUI reference as parameter type of {} declared in class {}",
                                m.getName(), allClass.getName());
                            badClasses.add(allClass);
                        }
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
            LOGGER.error("hashCode test skipped for type {}", cl, e);
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
            LOGGER.error("hashCode test skipped for type {}", cl, e);
        }
        return true;
    }

    /**
     * Tests that if <code>equals()</code> is overridden, <code>hashCode()</code> is also
     * overridden.
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
}
