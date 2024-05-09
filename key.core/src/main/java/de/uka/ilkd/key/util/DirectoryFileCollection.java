/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

import de.uka.ilkd.key.proof.io.consistency.FileRepo;

/**
 * This class is used to describe a directory structure as a repository for files to read in. A
 * directory is read recursively.
 *
 * All files are enumerated when the walker is created. Any file added afterwards will not looked at
 * when iterating.
 *
 * For more info see {@link FileCollection}
 *
 * @author MU
 */
public class DirectoryFileCollection implements FileCollection {

    /** directory under inspection */
    private final Path directory;

    /**
     * create a new File collection for a given directory The argument may be a single file also. A
     * directory is read recursively.
     *
     * @param directory
     *        directory to iterate through,
     */
    public DirectoryFileCollection(Path directory) {
        this.directory = directory;
    }

    /**
     * This method is to fix the bug: "0965: Creating arrays of primitive type fails when using
     * \bootclasspath " The method sorts the List of File that is given as parameter according to
     * the following criteria: - File paths that contain the subpath "java/lang" are stored before
     * other file paths. - If there is a File that contains the subpath "java/lang/Object.java" then
     * it is stored at the very beginning of the list.
     *
     * @author gladisch
     */
    private static void sortFiles(List<Path> files) {
        for (int a = 0; a < files.size() - 1; a++) {
            for (int b = a + 1; b < files.size(); b++) {
                if (!(a < b)) { throw new RuntimeException("Incorrect sorting algorithms."); }
                Path fa = files.get(a);
                Path fb = files.get(b);

                // Check if the path A contains the substring "JAVA/LANG"
                String pathA = fa.toString().toUpperCase().replace('\\', '/');
                boolean A_isObjectClass = pathA.contains("JAVA/LANG/OBJECT.JAVA");

                // Check if the path B contains the substring "JAVA/LANG/OBJECT.JAVA"
                String pathB = fb.toString().toUpperCase().replace('\\', '/');
                boolean B_inJavaLang = pathB.contains("JAVA/LANG");

                // Switch files to ensure the desired order of files
                if (B_inJavaLang && !A_isObjectClass) {
                    files.set(a, fb);
                    files.set(b, fa);
                }
            }
        }
    }


    /*
     * enumerate all files in a list and store that list in the walker.
     *
     * @see de.uka.ilkd.key.util.FileCollection#createWalker(java.lang.String)
     */
    public Walker createWalker(String extension) {
        return createWalker(new String[] { extension });
    }


    /*
     * enumerate all files in a list and store that list in the walker.
     *
     * @see de.uka.ilkd.key.util.FileCollection#createWalker(java.lang.String[])
     */
    public Walker createWalker(String[] extensions) {
        List<Path> files = new ArrayList<>();

        try (var stream = Files.walk(directory)) {
            stream.forEach(p -> {
                for (String extension : extensions) {
                    if (extension == null
                            || p.getFileName().toString().toLowerCase().endsWith(extension)) {
                        files.add(p);
                    }
                }
            });
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        sortFiles(files);
        return new Walker(files.iterator());
    }

    /*
     * This class keeps an internal list of files to be iterated that is created at construction
     * time.
     */
    private class Walker implements FileCollection.Walker {

        private final Iterator<Path> iterator;
        private Path currentFile;

        public Walker(Iterator<Path> iterator) {
            this.iterator = iterator;
        }

        public InputStream openCurrent() throws IOException {
            if (currentFile == null) {
                throw new NoSuchElementException();
            } else {
                return Files.newInputStream(currentFile);
            }

        }

        @Override
        public InputStream openCurrent(FileRepo fileRepo) throws IOException {
            if (fileRepo != null) {
                return fileRepo.getInputStream(currentFile);
            } else {
                return openCurrent(); // fallback without FileRepo
            }
        }

        @Override
        public Path getCurrentLocation() {
            return currentFile;
        }

        @Override
        public boolean step() {
            try {
                currentFile = iterator.next();
                return true;
            } catch (NoSuchElementException ex) {
                currentFile = null;
                return false;
            }
        }

        @Override
        public String getType() {
            return "file";
        }

        @Override
        public String getRelativeLocation() {
            return directory.relativize(currentFile).toString();
        }
    }

    @Override
    public String toString() {
        return "DirectoryFileCollection[" + directory + "]";
    }

}
