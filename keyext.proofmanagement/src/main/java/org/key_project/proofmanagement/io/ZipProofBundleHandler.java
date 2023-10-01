/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.io;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Stream;

import org.key_project.proofmanagement.check.PathNode;
import org.key_project.proofmanagement.check.ProofManagementException;
import org.key_project.util.java.IOUtil;

/**
 * A ProofBundleHandler for a proof bundle stored inside a zip file
 * (usually the file extension will be "zproof").
 * <br>
 * <b>Note:</b>
 * The current implementation unzips the bundle to a temporary directory.
 * These files are deleted automatically as soon as the ProofBundleHandler is closed.
 * All methods returning paths of files inside the bundle actually return paths
 * pointing to the temporary files!
 *
 * @author Wolfram Pfeifer
 */
public class ZipProofBundleHandler extends ProofBundleHandler {
    /** path of the actual proof bundle file */
    private final Path zipPath;

    /** indicates if the close() method has already been called */
    private boolean closed = false;

    // TODO: using ZipFileSystem is not possible, since KeY uses File objects as input
    // (a Path from a ZipFileSystemProvider can not be converted to a File)
    // Probably this part of KeY can be rewritten using Path instead of File?
    // private final FileSystem fs;

    /** path of the temporary directory the bundle contents are unzipped to */
    private final Path tmpDir;

    /**  */
    private final DirectoryProofBundleHandler dbh;

    /**
     * Create a new ZipProofBundleHandler for the zipped bundle with the given path.
     *
     * @param zipPath the path of the zip (usually, the file extension is "zproof")
     * @throws IOException if an I/O error occurs
     */
    ZipProofBundleHandler(Path zipPath) throws IOException {
        this.zipPath = zipPath;
        // fs = FileSystems.newFileSystem(zipPath, null);

        // extract to temporary directory and create a DirectoryProofBundleHandler for it
        tmpDir = Files.createTempDirectory("KeY_PM_unzip");
        IOUtil.extractZip(zipPath, tmpDir);
        dbh = new DirectoryProofBundleHandler(tmpDir);
    }

    // IMPORTANT: get... methods return paths to unzipped files!
    @Override
    public String getBundleName() {
        return zipPath.getFileName().toString();
    }

    @Override
    public Path getBundlePath() {
        return zipPath.toAbsolutePath().normalize();
    }

    @Override
    public Path relativize(Path path) {
        // we might need both cases
        if (path.startsWith(zipPath)) {
            return zipPath.relativize(path);
        } else {
            return tmpDir.relativize(path);
        }
    }

    @Override
    public List<Path> getProofFiles() throws ProofManagementException {
        // return getFiles(fs.getPath("/"), ProofBundleHandler.PROOF_MATCHER);
        return dbh.getProofFiles();
    }

    @Override
    public List<Path> getKeYFiles() throws IOException {
        // return getFiles(fs.getPath("/"), ProofBundleHandler.KEY_MATCHER);
        return dbh.getKeYFiles();
    }

    @Override
    public List<Path> getSourceFiles() throws IOException {
        // return getFiles(fs.getPath("/src"), ProofBundleHandler.SRC_MATCHER);
        return dbh.getSourceFiles();
    }

    @Override
    public List<Path> getClasspathFiles() throws IOException {
        // return getFiles(fs.getPath("/classpath"), ProofBundleHandler.SRC_MATCHER);
        return dbh.getClasspathFiles();
    }

    @Override
    public Path getBootclasspath() throws IOException {
        // return getFiles(fs.getPath("/bootclasspath"), ProofBundleHandler.BOOTCLASSPATH_MATCHER);
        return dbh.getBootclasspath();
    }

    @Override
    public PathNode getFileTree() throws IOException {
        // Path rootPath = fs.getPath("/");
        // PathNode root = new PathNode(null, rootPath);
        // Files.walkFileTree(rootPath, new TreeFileVisitor(root));
        // // prevent double inclusion of root directory itself
        // // TODO: check why this is necessary
        // return (PathNode) root.getChildren().first();

        return dbh.getFileTree();
    }

    @Override
    public Path getPath(String entryName) {
        // return fs.getPath(pathString);
        return dbh.getPath(entryName);
    }

    @Override
    public void close() throws IOException {
        // check if close has already been called
        if (!closed) {
            closed = true;
            // delete temporary content from disk
            try (Stream<Path> files = Files.walk(tmpDir)) {
                files.sorted(Comparator.reverseOrder())
                        .forEach(p -> {
                            try {
                                Files.delete(p);
                            } catch (IOException e) {
                                e.printStackTrace();
                            }
                        });
            }
        }
    }
}
