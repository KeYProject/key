/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.helper;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.*;
import java.util.Arrays;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (13.02.19)
 */
public final class FindResources {
    /**
     * List directory contents for a resource folder. Not recursive. This is basically a brute-force
     * implementation. Works for regular files and also JARs.
     *
     * @param clazz Any java class that lives in the same place as the resources you want.
     * @param path Should end with "/", but not start with one.
     * @return Just the name of each member item, not the full paths.
     * @throws URISyntaxException
     * @throws IOException
     * @author Greg Briggs
     */
    public static <T> List<Path> getResources(String path, Class<T> clazz)
            throws URISyntaxException, IOException {
        URL dirURL = clazz.getClassLoader().getResource(path);
        if (dirURL != null && dirURL.getProtocol().equals("file")) {
            /* A file path: easy enough */
            File[] files = new File(dirURL.toURI()).listFiles();
            Objects.requireNonNull(files);
            return Arrays.stream(files).map(File::toPath).collect(Collectors.toList());
        }

        if (dirURL == null) {
            /*
             * In case of a jar file, we can't actually find a directory. Have to assume the same
             * jar as clazz.
             */
            String me = clazz.getName().replace(".", "/") + ".class";
            dirURL = clazz.getClassLoader().getResource(me);
        }

        if (dirURL == null) {
            return null;
        }

        if ("jar".equals(dirURL.getProtocol())) {
            /* A JAR path */
            // strip out only the JAR file
            String jarPath = dirURL.getPath().substring(5, dirURL.getPath().indexOf('!'));
            try (FileSystem fs =
                FileSystems.newFileSystem(Paths.get(jarPath), clazz.getClassLoader())) {
                Path dir = fs.getPath(path);
                try (var s = Files.list(dir)) {
                    return s.collect(Collectors.toList());
                }
            }
        }
        throw new UnsupportedOperationException("Cannot list files for URL \"" + dirURL + "\"");
    }

    public static <T> List<Path> getResources(String path) throws URISyntaxException, IOException {
        return getResources(path, FindResources.class);
    }

    public static <T> Path getResource(String path, Class<T> clazz)
            throws URISyntaxException, IOException {
        URL dirURL = clazz.getClassLoader().getResource(path);
        if (dirURL != null && dirURL.getProtocol().equals("file")) {
            return new File(dirURL.toURI()).toPath();
        }

        if (dirURL == null) {
            /*
             * In case of a jar file, we can't actually find a directory. Have to assume the same
             * jar as clazz.
             */
            String me = clazz.getName().replace(".", "/") + ".class";
            dirURL = clazz.getClassLoader().getResource(me);
        }

        if (dirURL == null) {
            return null;
        }

        if (dirURL.getProtocol().equals("jar")) {
            /* A JAR path */
            // strip out only the JAR file
            String jarPath = dirURL.getPath().substring(5, dirURL.getPath().indexOf('!'));
            try (FileSystem fs =
                FileSystems.newFileSystem(Paths.get(jarPath), clazz.getClassLoader())) {
                return fs.getPath(path);
            }
        }
        throw new UnsupportedOperationException("Cannot list files for URL \"" + dirURL + "\"");
    }

    public static <T> Path getResource(String path) throws URISyntaxException, IOException {
        return getResource(path, FindResources.class);
    }

    /**
     * @param property
     * @param candidates
     * @return
     */
    public static File findFolder(String property, String... candidates) {
        return findFolder(true, property, candidates);
    }

    /**
     * Search for a folder.
     * <p>
     * The folder is searched by a value given via java system properties or by a list of
     * candidates.
     * <p>
     * You can specify whether the folder should exists or not. If the should exists the method
     * could return null.
     *
     * @param property a key for {@link System#getProperty(String)}
     * @param exists flag whether the folder should exists
     * @param candidates a list of candidates, used if <code>propertyName</code> is not set by the
     *        user
     * @return
     */
    public static File findFolder(boolean exists, String property, String... candidates) {
        if (System.getProperty(property) != null) {
            File f = new File(System.getProperty(property));
            if (f.exists() || !exists) {
                return f;
            }
        }
        for (String c : candidates) {
            File f = new File(c);
            if (f.exists() || !exists) {
                return f;
            }
        }
        return null;
    }

    public static File getExampleDirectory() {
        return findFolder("KEY_EXAMPLES_DIR", "key.ui/examples", "../key.ui/examples", "examples");
    }

    public static File getTestResultForRunAllProofs() {
        return findFolder(false, "KEY_TESTRESULT_RUNALLPROOFS", "build/reports/runallproofs");
    }

    public static File getTestCasesDirectory() {
        return findFolder("TEST_CASES", "src/test/resources/testcase");
    }

    public static File getTestResourcesDirectory() {
        return findFolder("TEST_RESOURCES", "src/test/resources/");
    }

    public static File getTacletProofsDirectory() {
        return findFolder("TACLET_PROOFS", "key.core/tacletProofs", "../key.core/tacletProofs",
            "tacletProofs");
    }
}
