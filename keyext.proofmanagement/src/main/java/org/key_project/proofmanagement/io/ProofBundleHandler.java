/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.io;

import java.io.Closeable;
import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.List;

import org.key_project.proofmanagement.check.PathNode;
import org.key_project.proofmanagement.check.ProofManagementException;

/**
 * Provides methods to collect paths of files inside a proof bundle.
 *
 * @author Wolfram Pfeifer
 */
public abstract class ProofBundleHandler implements Closeable {
    /**
     * This matcher matches *.proof files.
     */
    protected static final PathMatcher PROOF_MATCHER =
        FileSystems.getDefault().getPathMatcher("glob:**.proof");
    /**
     * This matcher matches *.key files.
     */
    protected static final PathMatcher KEY_MATCHER =
        FileSystems.getDefault().getPathMatcher("glob:**.key");
    /**
     * This matcher matches *.java files.
     */
    protected static final PathMatcher SRC_MATCHER =
        FileSystems.getDefault().getPathMatcher("glob:**.java");
    /**
     * This matcher matches *.java, *.class, *.zip, and *.jar files.
     */
    protected static final PathMatcher CLASSPATH_MATCHER =
        FileSystems.getDefault().getPathMatcher("glob:**.{java,class,zip,jar}");
    /**
     * This matcher matches *.java files.
     */
    protected static final PathMatcher BOOTCLASSPATH_MATCHER =
        FileSystems.getDefault().getPathMatcher("glob:**.java");

    /**
     * Returns the name of the proof bundle.
     *
     * @return the name as a String
     */
    public abstract String getBundleName();

    /**
     * Returns the root path of the proof bundle.
     *
     * @return the path of the bundle
     */
    public abstract Path getBundlePath();

    /**
     * Relativies the input path with respect to the bundle root.
     *
     * @param path the path to relativize, assumed to point to a file in the bundle
     * @return the input path relative to the bundle root
     */
    public abstract Path relativize(Path path);

    /**
     * Returns a list of all paths to *.proof files in the bundle. Only *.proof files residing
     * top-level in the bundle are considered.
     *
     * @return a list of paths to the *.proof files
     * @throws ProofManagementException if the bundle can not be opened/accessed
     */
    public abstract List<Path> getProofFiles() throws ProofManagementException;

    /**
     * Returns a list of all paths to *.key files in the bundle. Only *.key files residing
     * top-level in the bundle are considered.
     *
     * @return a list of paths to the *.key files
     * @throws IOException if the bundle can not be opened/accessed
     */
    public abstract List<Path> getKeYFiles() throws IOException;

    /**
     * Returns a list of all paths to Java source files in the bundle. Only *.java files residing
     * inside the <code>src</code> subfolder are considered.
     *
     * @return a list of paths to the source files
     * @throws IOException if the bundle can not be opened/accessed
     */
    public abstract List<Path> getSourceFiles() throws IOException;

    /**
     * Returns a list of all classpath files in the bundle. This includes only files inside the
     * <code>classpath</code> subfolder. Considered file extensions are "java", "class",
     * "zip" and "jar".
     *
     * @return a list of paths to the classpath files
     * @throws IOException if the bundle can not be opened/accessed
     */
    public abstract List<Path> getClasspathFiles() throws IOException;

    /**
     * Returns the bootclasspath of the bundle. This is the <code>bootclasspath</code> subfolder,
     * if it exists. Otherwise null is returned.
     *
     * @return the bootclasspath or null, if none is specified
     * @throws IOException if the bundle can not be opened/accessed
     */
    public abstract Path getBootclasspath() throws IOException;

    /**
     * Returns a tree of the complete file hierarchy inside the bundle.
     *
     * @return the file tree of the bundle
     * @throws IOException if the bundle can not be opened/accessed
     */
    public abstract PathNode getFileTree() throws IOException;

    /**
     * Creates a path to the entry with the given name inside the bundle.
     *
     * @param entryName the entry name inside the bundle
     * @return the path of the entry
     */
    public abstract Path getPath(String entryName);

    /**
     * Static factory method to create a ProofBundleHandler based on the type of the proof bundle
     * (zipped bundle or directory).
     *
     * @param root the path of the proof bundle
     * @return a bundle handler suited for opening the type of proof bundle <code>root</code>
     *         points to.
     * @throws IOException if the bundle can not be opened/accessed
     */
    public static ProofBundleHandler createBundleHandler(Path root) throws IOException {
        if (Files.isDirectory(root)) {
            return new DirectoryProofBundleHandler(root);
        } else {
            return new ZipProofBundleHandler(root);
        }
    }

    /**
     * A FileVisitor for creating a file tree from the visited paths.
     */
    protected static class TreeFileVisitor extends SimpleFileVisitor<Path> {
        /** the node corresponding the currently visited directory */
        private PathNode current;

        /**
         * Create a new TreeFileVisitor with the given start node.
         *
         * @param start the root node of the tree
         */
        public TreeFileVisitor(PathNode start) {
            this.current = start;
        }

        @Override
        public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) {
            PathNode node = new PathNode(current, dir);
            current.addChild(node);
            current = node; // descend in tree
            return FileVisitResult.CONTINUE;
        }

        @Override
        public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) {
            PathNode node = new PathNode(current, file);
            current.addChild(node);
            return FileVisitResult.CONTINUE;
        }

        @Override
        public FileVisitResult postVisitDirectory(Path dir, IOException exc) {
            current = current.getParent(); // ascend in tree
            return FileVisitResult.CONTINUE;
        }
    }
}
