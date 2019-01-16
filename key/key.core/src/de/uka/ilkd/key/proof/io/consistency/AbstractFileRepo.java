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

/**
 * Abstract repo implementation to perform tasks independent from the concrete way the files are
 * cached. This mainly includes saving of all files registered to the repo as well as adapting the
 * references (e.g. "javaPath") in *.key files.
 *
 * @author Wolfram Pfeifer
 */
public abstract class AbstractFileRepo implements FileRepo {
    // TODO: paths are assumed to be absolute and normalized
    /** The original java source path. */
    protected Path javaPath;

    /** The original class path. */
    protected List<Path> classpath;

    /**
     * The boot class path, that is, the path to the folder where stubs of library classes
     * (e.g. Object, List, ...) used in KeY are stored.
     */
    protected Path bootclasspath;

    /**
     * The base directory of the loaded proof (needed to calculate relative paths).
     * If a .key/.proof file is loaded, this should be set to the path specified via "javaSource".
     * If a directory is loaded, baseDir should be set to the path of the directory.
     */
    protected Path baseDir;

    /**
     * Stores original paths of all files stored in the repo.
     * The paths stored here have to respect the repo structure with src folder,
     * .key files top-level, ...
     */
    protected Set<Path> files = new HashSet<Path>();

    /**
     * This flag indicates that the Repo and all data in it have been deleted.
     */
    protected boolean disposed = false;
    
    protected boolean isInJavaPath(Path path) {
        return javaPath != null && path.startsWith(javaPath);
    }
    
    protected boolean isInBootClassPath(Path path) {
        return bootclasspath != null && path.startsWith(bootclasspath);
    }

    @Override
    public void saveProof(Path savePath, Proof proof) throws IOException {
        // TODO: allow overwriting existing files (delete first?)

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
                is = getInputStream(p);
            }

            // we use a this method instead of IOUtil.copy() because zos must not be closed
            copy(is, zos);
            is.close();

            zos.closeEntry();
        }
        zos.close();
    }

    /**
     * Can be used to get an InputStream (concrete implementation depends on concrete repo)
     * of the resource.
     * @param p the filename of the requested file
     * @return an InputStream of the resource or null if it has not been stored in the repo before.
     * @throws FileNotFoundException if the file exists, is a directory, or can not be opened
     */
    protected abstract InputStream getInputStream(Path p) throws FileNotFoundException;

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

        // get the concrete source from the repo
        InputStream is = getInputStream(p);

        // TODO: adapt include/includeFile
        try (Stream<String> lines = new BufferedReader(new InputStreamReader(is)).lines()) {
            // TODO: may produce multiple occurrences of same classpath statement
            // create an in-memory copy of the file, modify it, and return an InputStream
            String rep = lines                  // TODO: check regular expressions
                .map(l -> l.replaceAll("\\\\javaSource \\\".*\\\";",
                                       "\\\\javaSource \"src\";"))
                .map(l -> l.replaceAll("\\\\classpath \\\".*\\\";",
                                       "\\\\classpath \"classpath\";"))
                .map(l -> l.replaceAll("\\\\bootclasspath \\\".*\\\";",
                                       "\\\\bootclasspath \"bootclasspath\";"))
                .collect(Collectors.joining(System.lineSeparator()));
            is.close(); // TODO: ensure this is executed

            ByteArrayInputStream bais = new ByteArrayInputStream(rep.getBytes("UTF-8"));
            return bais;
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
        // path can be a file or a directory
        if (Files.isDirectory(path)) {
            baseDir = path.toAbsolutePath().normalize();
        } else {
            baseDir = path.getParent().toAbsolutePath().normalize();
        }
    }

    @Override
    public Path getBaseDir() {
        return baseDir;
    }

    @Override
    public void dispose() {
        // delete all references
        javaPath = null;
        classpath = null;
        bootclasspath = null;
        baseDir = null;

        disposed = true;
    }
}
