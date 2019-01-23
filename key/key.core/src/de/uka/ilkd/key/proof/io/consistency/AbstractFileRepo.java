package de.uka.ilkd.key.proof.io.consistency;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;

/**
 * Abstract repo implementation to perform tasks independent from the concrete way the files are
 * cached. This mainly includes saving of all files registered to the repo as well as adapting the
 * references (e.g. "javaPath") in *.key files.
 *
 * @author Wolfram Pfeifer
 */
public abstract class AbstractFileRepo implements FileRepo {

    /** The original java source path (absolute and normalized). */
    protected Path javaPath;

    /** The original class path (absolute and normalized). */
    protected List<Path> classpath;

    /**
     * The boot class path, that is, the path to the folder where stubs of library classes
     * (e.g. Object, List, ...) used in KeY are stored.
     * The path stored here is absolute and normalized.
     */
    protected Path bootclasspath;

    /**
     * The base directory of the loaded proof (needed to calculate relative paths).
     * If a .key/.proof file is loaded, this should be set to the path specified via "javaSource".
     * If a directory is loaded, baseDir should be set to the path of the directory.
     * The path stored here is absolute and normalized.
     */
    protected Path baseDir;

    /**
     * Stores the source paths of all files that have been copied to the repo as absolute paths.
     * In addition, all files (usually proofs) that are saved in the repo via the method
     * {@link #createOutputStream(Path)} are stored here. These files are stored as relative paths
     * respecting the repo structure, because they have no counterpart outside the repo.
     *
     * When the method {@link #saveProof(Path, Proof)} is called, all files registered here will
     * be saved.
     */
    protected Set<Path> files = new HashSet<>();

    /**
     * This set stores all proofs that use this repo. When it gets empty, the repo is disposed.
     */
    protected Set<Proof> registeredProofs = new HashSet<>();

    /**
     * This flag indicates that the repo and all data in it have been deleted.
     */
    protected boolean disposed = false;

    /**
     * Checks if the given path is inside the Java path
     * @param path the path to check
     * @return true if the path is inside the Java path and false if not
     */
    protected boolean isInJavaPath(Path path) {
        return javaPath != null && path.startsWith(javaPath);
    }

    /**
     * Checks if the given path is inside the boot class path
     * @param path the path to check
     * @return true if the path is inside the boot class path and false if not
     */
    protected boolean isInBootClassPath(Path path) {
        return bootclasspath != null && path.startsWith(bootclasspath);
    }

    @Override
    public void saveProof(Path savePath) throws IOException {
        // We overwrite an existing proof here in any case. Checks have to be done earlier.
        if (Files.exists(savePath)) {
            Files.delete(savePath);
        }

        // create actual ZIP file (plus its directory if not existent)
        Files.createDirectories(savePath.getParent());
        Files.createFile(savePath);

        // filtering for *.key/*.proof files
        PathMatcher matcher = FileSystems.getDefault().getPathMatcher("glob:**.{key,proof}");

        // write files to ZIP
        ZipOutputStream zos = new ZipOutputStream(Files.newOutputStream(savePath));
        Iterator<Path> it = files.iterator();

        while (it.hasNext()) {
            Path p = it.next();
            // use the correct name for saving!
            zos.putNextEntry(new ZipEntry(getSaveName(p).toString()));

            InputStream is;
            if (matcher.matches(p)) {
                // adapt file references to point to the copied files
                is = adaptFileRefs(p);
            } else {
                // open InputStream to file without modification
                is = getInputStreamInternal(p);
            }

            // we use this method instead of IOUtil.copy() because zos must not be closed
            copy(is, zos);
            is.close();

            zos.closeEntry();
        }
        zos.close();
    }

    /**
     * Return the save name for a given file.
     * @param path the given file (absolute or relative to the proof base directory)
     * @return the name (may include subdirectories) the file should have in proof package, that is
     *      a path relative to the root of the package
     */
    protected abstract Path getSaveName(Path path);

    /**
     * Can be used to get a direct InputStream to a file stored in the FileRepo.
     * The concrete implementation depends on the concrete FileRepo.
     * @param p the original path (outside the FileRepo) of the requested file
     * @return an InputStream of the resource or null if it has not been stored in the FileRepo
     *      before.
     * @throws FileNotFoundException if the does not file exist, is a directory,
     *      or can not be opened
     */
    protected abstract InputStream getInputStreamInternal(Path p) throws FileNotFoundException;

    /**
     * Variation of the method IOUtil.copy():
     * Copies the content of InputStream to OutputStream <b>without closing any of them</b>.
     * @param source the source of the copy operation
     * @param target the target of the copy operation
     * @return true if copy was performed and false if not performed
     * @throws IOException if an I/O error occurs
     */
    public static boolean copy(InputStream source, OutputStream target) throws IOException {
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
     * Rewrites the file references inside of .key/.proof files such that the point correctly to
     * the copied files in the ZIP file.
     * @param p the path of the file where the references are adapted
     * @return an InputStream to a (in-memory) copy of the file
     * @throws IOException if an I/O error occurs
     */
    protected InputStream adaptFileRefs(Path p) throws IOException {
        // TODO: adapt include/includeFile (e.g. for Taclets)
        // TODO: may produce multiple occurrences of same classpath statement

        try (InputStream is = getInputStreamInternal(p);  // get concrete source from repo
             Stream<String> lines = new BufferedReader(new InputStreamReader(is)).lines()) {

            // create an in-memory copy of the file, modify it, and return an InputStream
            String rep = lines
                .map(l -> l.replaceAll("\\\\javaSource \\\".*\\\";",
                                       "\\\\javaSource \"src\";"))
                .map(l -> l.replaceAll("\\\\classpath \\\".*\\\";",
                                       "\\\\classpath \"classpath\";"))
                .map(l -> l.replaceAll("\\\\bootclasspath \\\".*\\\";",
                                       "\\\\bootclasspath \"bootclasspath\";"))
                .collect(Collectors.joining(System.lineSeparator()));

            return new ByteArrayInputStream(rep.getBytes("UTF-8"));
        }
    }

    @Override
    public void setBootClassPath(File path) {
        if (path != null) {
            bootclasspath = path.toPath().toAbsolutePath().normalize();
        }
    }

    @Override
    public void setClassPath(List<File> paths) {
        if (paths != null) {
            classpath = paths.stream()
                    .filter(p -> p != null)             // to be sure it contains no null elements
                                                        // convert Files to Paths and normalize
                    .map(p -> p.toPath().toAbsolutePath().normalize())
                    .collect(Collectors.toList());
        }
    }

    @Override
    public void setJavaPath(String path) {
        if (path != null) {
            javaPath = Paths.get(path).toAbsolutePath().normalize();
        }
    }

    @Override
    public void setBaseDir(Path path) {
        /* Path can be a file or a directory. In case of a file the complete containing directory
         * is read in. */
        if (Files.isDirectory(path)) {
            baseDir = path.toAbsolutePath().normalize();
        } else {
            baseDir = path.getParent().toAbsolutePath().normalize();
        }
    }

    @Override
    public void registerProof(Proof proof) {
        registeredProofs.add(proof);
        // register the repo in the proof to listen to ProofDisposedEvents.
        proof.addProofDisposedListener(this);
    }

    /**
     * Clears all data in the FileRepo and marks it as disposed.
     */
    protected void dispose() {
        // delete all references
        javaPath = null;
        classpath = null;
        bootclasspath = null;
        baseDir = null;

        files.clear();
        files = null;
        registeredProofs = null;   // this set is already empty, else the repo must not be disposed

        disposed = true;
    }

    @Override
    public void proofDisposing(ProofDisposedEvent e) {
        // TODO not used?
    }

    @Override
    public void proofDisposed(ProofDisposedEvent e) {
        Proof source = e.getSource();
        source.removeProofDisposedListener(this);

        // remove proof from registered proofs
        registeredProofs.remove(source);
        if (registeredProofs.isEmpty()) {
            // empty repo -> clear all data in the repo (e.g. files, arrays)
            dispose();
        }
    }
}
