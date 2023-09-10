/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.io;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.key_project.proofmanagement.check.PathNode;
import org.key_project.proofmanagement.check.ProofManagementException;

/**
 * ProofBundleHandler for a directory that respects the bundle file hierarchy.
 *
 * @author Wolfram Pfeifer
 */
public class DirectoryProofBundleHandler extends ProofBundleHandler {
    /** the path of the root directory of the bundle */
    private final Path rootPath;

    /**
     * Creates a new DirectoryProofBundleHandler for a directory with the given path.
     *
     * @param rootPath the path of the root directory of the bundle
     */
    DirectoryProofBundleHandler(Path rootPath) {
        this.rootPath = rootPath;
    }

    /**
     * Creates a list of those paths of files/directories inside the given directory that are
     * matched by given matcher. The method does not recursively descend into subdirectories.
     *
     * @param directory the directory to list
     * @param matcher the matcher for filtering
     * @return the list of paths
     * @throws IOException if the directory can not be opened
     */
    private static List<Path> getFiles(Path directory, PathMatcher matcher) throws IOException {
        if (Files.isDirectory(directory)) {
            // IMPORTANT: use try-with-resources here to ensure the stream is closed and does not
            // prevent the files from deletion on Windows!
            try (Stream<Path> stream = Files.list(directory)) {
                return stream.filter(matcher::matches)
                        .collect(Collectors.toList());
            }
        }
        return Collections.emptyList();
    }

    @Override
    public String getBundleName() {
        return rootPath.getFileName().toString();
    }

    @Override
    public Path getBundlePath() {
        return rootPath.toAbsolutePath().normalize();
    }

    @Override
    public Path relativize(Path path) {
        return rootPath.toAbsolutePath().normalize().relativize(path);
    }

    @Override
    public List<Path> getProofFiles() throws ProofManagementException {
        try {
            return getFiles(rootPath, ProofBundleHandler.PROOF_MATCHER);
        } catch (IOException e) {
            // we wrap the exception, this allows for easier Checker interface
            throw new ProofManagementException("Can no access the proof bundle.", e);
        }
    }

    @Override
    public List<Path> getKeYFiles() throws IOException {
        return getFiles(rootPath, ProofBundleHandler.KEY_MATCHER);
    }

    @Override
    public List<Path> getSourceFiles() throws IOException {
        Path srcPath = rootPath.resolve(Paths.get("src"));
        return getFiles(srcPath, ProofBundleHandler.SRC_MATCHER);
    }

    @Override
    public List<Path> getClasspathFiles() throws IOException {
        Path classpath = rootPath.resolve(Paths.get("classpath"));
        return getFiles(classpath, ProofBundleHandler.CLASSPATH_MATCHER);
    }

    @Override
    public Path getBootclasspath() throws IOException {
        Path bootclasspath = rootPath.resolve(Paths.get("bootclasspath"));
        if (Files.isDirectory(bootclasspath)) {
            return bootclasspath;
        }
        return null;
    }

    @Override
    public PathNode getFileTree() throws IOException {
        PathNode root = new PathNode(null, rootPath);
        Files.walkFileTree(rootPath, new TreeFileVisitor(root));
        // prevent double inclusion of root directory itself
        // TODO: check why this is necessary
        return (PathNode) root.getChildren().first();
    }

    @Override
    public Path getPath(String entryName) {
        return rootPath.resolve(entryName);
    }

    @Override
    public void close() throws IOException {
        // nothing to do
    }
}
