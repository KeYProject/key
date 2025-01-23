/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.io.consistency;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.MalformedURLException;
import java.net.URL;
import java.nio.file.*;
import java.util.HashSet;
import java.util.Set;

import org.key_project.rusty.proof.io.RuleSource;

public abstract class AbstractFileRepo implements FileRepo {

    /**
     * This matcher matches *.java files.
     */
    protected static final PathMatcher RUST_MATCHER =
        FileSystems.getDefault().getPathMatcher("glob:**.rs");

    /**
     * A matcher matches *.key and *.proof files.
     */
    protected static final PathMatcher KEY_MATCHER =
        FileSystems.getDefault().getPathMatcher("glob:**.{key,proof}");

    /**
     * The base directory of the loaded proof (needed to calculate relative paths). If a .key/.proof
     * file is loaded, this should be set to the path specified via "javaSource". If a directory is
     * loaded, baseDir should be set to the path of the directory. The path stored here is absolute
     * and normalized.
     */
    private Path baseDir;

    /**
     * Stores the source paths of all files that have been copied to the repo as absolute paths. In
     * addition, all files (usually proofs) that are saved in the repo via the method
     * {@link #createOutputStream(Path)} are stored here. These files are stored as relative paths
     * respecting the repo structure, because they have no counterpart outside the repo.
     *
     * When the method {@link #saveProof(Path)} is called, all files registered here will be saved.
     */
    private Set<Path> files = new HashSet<>();

    /** The original Rust source path (absolute and normalized). */
    private Path rustPath;

    /**
     * Variation of the method IOUtil.copy(): Copies the content of InputStream to OutputStream
     * <b>without closing any of them</b>.
     *
     * @param source the source of the copy operation
     * @param target the target of the copy operation
     * @return true if copy was performed and false if not performed
     * @throws IOException if an I/O error occurs
     */
    private static boolean copy(InputStream source, OutputStream target) throws IOException {
        if (source != null && target != null) {
            byte[] buffer = new byte[1024];
            int read;
            while ((read = source.read(buffer)) >= 1) {
                target.write(buffer, 0, read);
            }
            return true;
        } else {
            return false;
        }
    }

    /**
     * Copyies the file at source path to the target path and creates parent directories if
     * required.
     *
     * @param source path of the source file
     * @param target path of the target file
     * @throws IOException if an I/O error occurs (e.g. user has no permission to write target)
     */
    protected static void createDirsAndCopy(Path source, Path target) throws IOException {
        Files.createDirectories(target.getParent());
        Files.copy(source, target);
    }

    /**
     * Tests if the given path references an internal file in KeY, i.e. if it is inside JavaRedux or
     * rules folder.
     *
     * @param path the path to test
     * @return true iff it is an internal file
     * @throws MalformedURLException if the path can not be converted to an URL
     */
    protected static boolean isInternalFile(Path path) throws MalformedURLException {
        URL url = path.toUri().toURL();
        return isInternalResource(url);
    }

    /**
     * Tests if the given URL references an internal resource of KeY, i.e. if it is a Java or rule
     * file shipped with KeY (may be inside a jar file).
     *
     * @param url the url to test
     * @return true iff the file is an internal file
     */
    protected static boolean isInternalResource(URL url) {
        String urlStr = url.toString();
        String rulesURLStr = "rules";
        return urlStr.startsWith(rulesURLStr);

    }

    protected Path getBaseDir() {
        return baseDir;
    }

    /**
     * Adds the given file to the list of files to save.
     *
     * @param p the path of the file to add
     */
    protected void addFile(Path p) {
        files.add(p);
    }

    @Override
    public InputStream getInputStream(Path path) throws IOException {
        // wrap path into URL for uniform treatment
        return getInputStream(path.toUri().toURL());
    }

    @Override
    public InputStream getInputStream(RuleSource ruleSource) throws IOException {
        return getInputStream(ruleSource.url());
    }

    @Override
    public void setRustyPath(String path) throws IllegalStateException {
        if (rustPath != null) {
            throw new IllegalStateException("Rust path is already set!");
        }
        if (path != null) {
            rustPath = Paths.get(path).toAbsolutePath().normalize();
        }
    }

    @Override
    public void setBaseDir(Path path) {
        /*
         * Path can be a file or a directory. In case of a file the complete containing directory is
         * read in.
         */
        // solves #1524: make paths absolute first to avoid NPE
        Path absolute = path.toAbsolutePath();
        if (Files.isDirectory(path)) {
            baseDir = absolute.normalize();
        } else {
            baseDir = absolute.getParent().normalize();
        }
    }

    /**
     * Return the save name for a given file.
     *
     * @param path the given file (absolute or relative to the proof base directory)
     * @return the name (may include subdirectories) the file should have in proof package, that is
     *         a path relative to the root of the package
     */
    protected abstract Path getSaveName(Path path);

    /**
     * Can be used to get a direct InputStream to a file stored in the FileRepo. The concrete
     * implementation depends on the concrete FileRepo.
     *
     * @param p the original path (outside the FileRepo) of the requested file
     * @return an InputStream of the resource or null if it has not been stored in the FileRepo
     *         before.
     * @throws FileNotFoundException if the does not file exist, is a directory, or can not be
     *         opened
     */
    protected abstract InputStream getInputStreamInternal(Path p) throws FileNotFoundException;

    protected Path getRustPath() {
        return rustPath;
    }

    /**
     * Checks if the given path is inside the Java path
     *
     * @param path the path to check
     * @return true if the path is inside the Java path and false if not
     */
    protected boolean isInRustPath(Path path) {
        return rustPath != null && path.startsWith(rustPath);
    }

}
