/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.io.consistency;

import java.io.*;
import java.net.MalformedURLException;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

import de.uka.ilkd.key.java.JavaService;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.util.KeYResourceManager;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Abstract repo implementation to perform tasks independent from the concrete way the files are
 * cached. This mainly includes saving of all files registered to the repo as well as adapting the
 * references (e.g. "javaPath") in *.key files.
 *
 * @author Wolfram Pfeifer
 */
@NullMarked
public abstract class AbstractFileRepo implements FileRepo {
    /**
     * The URL to KeY's built-in rules (used to prevent built-in rules from getting copied).
     */
    protected static final URL RULES_URL = Objects.requireNonNull(
        KeYResourceManager.getManager().getResourceFile(Proof.class, "rules/"),
        "built-in rules directory is an essential part of KeY");

    /**
     * The URL to KeY's built-in Java classes (used to prevent these classes from getting copied).
     */
    protected static final URL REDUX_URL = Objects.requireNonNull(
        KeYResourceManager.getManager().getResourceFile(JavaService.class, "JavaRedux/"),
        "built-in Java class stubs are an essential part of KeY");

    /**
     * This matcher matches *.java files.
     */
    protected static final PathMatcher JAVA_MATCHER =
        FileSystems.getDefault().getPathMatcher("glob:**.{java,jml}");

    /**
     * A matcher matches *.key and *.proof files.
     */
    protected static final PathMatcher KEY_MATCHER =
        FileSystems.getDefault().getPathMatcher("glob:**.{key,proof}");

    /**
     * This matcher matches *.zip and *.jar files.
     */
    protected static final PathMatcher ZIP_MATCHER =
        FileSystems.getDefault().getPathMatcher("glob:**.{zip,jar}");

    /**
     * This matcher matches *.class files.
     */
    protected static final PathMatcher CLASS_MATCHER =
        FileSystems.getDefault().getPathMatcher("glob:**.class");

    /** The original java source path (absolute and normalized). */
    private @Nullable Path javaPath;

    /** The original class path (absolute and normalized). */
    private @Nullable List<Path> classpath;

    /**
     * The boot class path, that is, the path to the folder where stubs of library classes (e.g.
     * Object, List, ...) used in KeY are stored. The path stored here is absolute and normalized.
     */
    private @Nullable Path bootclasspath;

    /**
     * The base directory of the loaded proof (needed to calculate relative paths). If a .key/.proof
     * file is loaded, this should be set to the path specified via "javaSource". If a directory is
     * loaded, baseDir should be set to the path of the directory. The path stored here is absolute
     * and normalized.
     */
    private @Nullable Path baseDir;

    /**
     * Stores the source paths of all files that have been copied to the repo as absolute paths. In
     * addition, all files (usually proofs) that are saved in the repo via the method
     * {@link #createOutputStream(Path)} are stored here. These files are stored as relative paths
     * respecting the repo structure, because they have no counterpart outside the repo.
     *
     * When the method {@link #saveProof(Path)} is called, all files registered here will be saved.
     */
    private Set<Path> files = new HashSet<>();

    /**
     * This set stores all proofs that use this repo. When it gets empty, the repo is disposed.
     */
    private Set<Proof> registeredProofs = new HashSet<>();

    /**
     * This flag indicates that the repo and all data in it have been deleted.
     */
    private boolean disposed = false;

    /**
     * Variation of the method IOUtil.copy(): Copies the content of InputStream to OutputStream
     * <b>without closing any of them</b>.
     *
     * @param source the source of the copy operation
     * @param target the target of the copy operation
     * @return true if copy was performed and false if not performed
     * @throws IOException if an I/O error occurs
     */
    private static boolean copy(@Nullable InputStream source, @Nullable OutputStream target)
            throws IOException {
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
        Files.createDirectories(Objects.requireNonNull(target.getParent()));
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
        String rulesURLStr = RULES_URL.toString();
        String reduxURLStr = REDUX_URL.toString();
        return urlStr.startsWith(rulesURLStr) || urlStr.startsWith(reduxURLStr);
    }

    public String calcDirectorySHA1(Path d) throws IOException, NoSuchAlgorithmException {
        StringBuilder sb = new StringBuilder();
        // Since the checksum is highly order-dependent, sort the files in each directory by name
        Files.walk(d).filter(Files::isRegularFile).sorted(Path::compareTo).forEachOrdered(p -> {
            try {
                String h = calcFileSHA1(p);
                System.out.println("SHA1 of " + p + ": " + h);
                sb.append(h);
            } catch (IOException e) {
                throw new UncheckedIOException(e);
            } catch (NoSuchAlgorithmException e) {
                throw new RuntimeException(e);
            }
        });
        System.out.println(sb.toString());
        byte[] digest = MessageDigest.getInstance("SHA1").digest(sb.toString().getBytes());

        StringBuilder hexString = new StringBuilder();
        for (byte b : digest) {
            hexString.append(String.format("%02x", b));
        }
        return hexString.toString();
    }

    public String calcFileSHA1(Path p) throws IOException, NoSuchAlgorithmException {
        // TODO: check that p refers to a file
        byte[] content = Files.readAllBytes(p);
        byte[] digest = MessageDigest.getInstance("SHA1").digest(content);

        StringBuilder hexString = new StringBuilder();
        for (byte b : digest) {
            hexString.append(String.format("%02x", b));
        }
        return hexString.toString();
    }

    protected @Nullable Path getJavaPath() {
        return javaPath;
    }

    protected boolean isDisposed() {
        return disposed;
    }

    protected @Nullable List<Path> getClasspath() {
        return classpath;
    }

    protected @Nullable Path getBootclasspath() {
        return bootclasspath;
    }

    protected @Nullable Path getBaseDir() {
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

    protected Set<Proof> getRegisteredProofs() {
        return registeredProofs;
    }

    /**
     * Checks if the given path is inside the Java path
     *
     * @param path the path to check
     * @return true if the path is inside the Java path and false if not
     */
    protected boolean isInJavaPath(Path path) {
        return javaPath != null && path.startsWith(javaPath);
    }

    /**
     * Checks if the given path is inside the boot class path
     *
     * @param path the path to check
     * @return true if the path is inside the boot class path and false if not
     */
    protected boolean isInBootClassPath(Path path) {
        return bootclasspath != null && path.startsWith(bootclasspath);
    }

    /**
     * Stores all files stored in the FileRepo in a consistent package as a ZIP archive at the given
     * target path. If a file with the given path exists, it is deleted first.
     *
     * @param savePath the target path of the ZIP archive
     * @throws IOException on IO errors, e.g. if the user has no permission to write at the path
     *         <p>
     *         Every file stored in the repository has a save name, and the open input stream is
     *         always
     *         present at the close site; the dereferences of the (nullable) save name and
     *         (nullable)
     *         input stream are suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    public void saveProof(Path savePath) throws IOException {
        // We overwrite an existing proof here in any case. Checks have to be done earlier.
        if (Files.exists(savePath)) {
            Files.delete(savePath);
        }

        // create actual ZIP file (plus its directory if not existent)
        Files.createDirectories(Objects.requireNonNull(savePath.getParent()));
        Files.createFile(savePath);

        // write files to ZIP
        ZipOutputStream zos = new ZipOutputStream(Files.newOutputStream(savePath));

        for (Path p : files) {

            // use the correct name for saving!
            // fix for #1655: replace separators to conform to zip specification (only slashes)!
            String entryName = getSaveName(p).toString();
            if (File.separatorChar != '/') {
                entryName = entryName.replace(File.separatorChar, '/');
            }
            zos.putNextEntry(new ZipEntry(entryName));

            InputStream is;
            // filtering for *.key/*.proof files
            if (KEY_MATCHER.matches(p)) {
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
     *
     * @param path the given file (absolute or relative to the proof base directory)
     * @return the name (may include subdirectories) the file should have in proof package, that is
     *         a path relative to the root of the package
     */
    protected abstract @Nullable Path getSaveName(Path path);

    @Override
    public InputStream getInputStream(Path path) throws IOException {
        // wrap path into URL for uniform treatment
        InputStream is = getInputStream(path.toUri().toURL());
        if (is == null) {
            throw new FileNotFoundException("File not stored in the file repository: " + path);
        }
        return is;
    }

    @Override
    public InputStream getInputStream(RuleSource ruleSource) throws IOException {
        InputStream is = getInputStream(ruleSource.url());
        if (is == null) {
            throw new FileNotFoundException(
                "Rule source not stored in the file repository: " + ruleSource.url());
        }
        return is;
    }

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
    protected abstract @Nullable InputStream getInputStreamInternal(Path p)
            throws FileNotFoundException;

    /**
     * Rewrites the file references inside of .key/.proof files such that the point correctly to the
     * copied files in the ZIP file.
     *
     * @param p the path of the file where the references are adapted
     * @return an InputStream to a (in-memory) copy of the file
     * @throws IOException if an I/O error occurs
     */
    protected InputStream adaptFileRefs(Path p) throws IOException {
        // TODO: adapt include/includeFile (e.g. for Taclets)
        // TODO: may replace/filter too much (e.g. in comments)

        try (InputStream is = Objects.requireNonNull(getInputStreamInternal(p),
            "file " + p + " is not stored in the repository");
                Stream<String> lines =
                    new BufferedReader(new InputStreamReader(is, StandardCharsets.UTF_8)).lines()) {

            // create an in-memory copy of the file, modify it, prepend the classpath,
            // and return an InputStream
            String rep = lines // remove all classpath declarations
                    .filter(l -> !l.matches(".*\\\\classpath \".*\";.*"))
                    .map(l -> l.replaceAll("\\\\javaSource \".*\";", "\\\\javaSource \"src\";"))
                    .map(l -> l.replaceAll("\\\\bootclasspath \".*\";",
                        ""))
                    .collect(Collectors.joining(System.lineSeparator()));

            // add classpath (has to be prior to javaSource)
            rep = addClasspath(rep);

            return new ByteArrayInputStream(rep.getBytes(StandardCharsets.UTF_8));
        }
    }

    /**
     * Adds the classpath String for all paths in classpath to the given String representing the
     * content of a .key/.proof file. The classpath Strings are inserted at the correct position:
     * Directly in front of "\javaSource ...", if existing, or else in front of other "\classpath
     * ..." declarations.
     *
     * @param keyFileContent a String containing the content of a .key/.proof file.
     * @return the modified content of the file with inserted "\classpath ..." declarations.
     *         <p>
     *         A class-path entry of the repository always maps to a save name; the dereference of
     *         the
     *         (nullable) save name is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    private String addClasspath(String keyFileContent) {
        if (classpath == null || classpath.isEmpty()) {
            return keyFileContent;
        }

        // build a String with all classpaths
        StringBuilder sb = new StringBuilder();
        for (Path t : classpath) {
            sb.append("\\classpath \"");

            Path cp;
            if (Files.isRegularFile(t)) {
                // t denotes a zip/jar file -> request savename (depends on subclass)
                cp = getSaveName(t);
            } else {
                // t denotes a directory in classpath -> add "classpath/dir_name"
                cp = Paths.get("classpath").resolve(Objects.requireNonNull(t.getFileName()));
            }

            // replace separator by '/' to avoid problems on Windows
            String replaced = cp.toString().replace(FileSystems.getDefault().getSeparator(), "/");

            sb.append(replaced);
            sb.append("\";");
            sb.append(System.lineSeparator());
        }

        // either javaSource or classpath must be specified -> find it
        int index = keyFileContent.indexOf("\\javaSource");
        if (index == -1) { // classpath must be present
            index = keyFileContent.indexOf("\\classpath");
        }

        // fallback: insert at beginning of String
        if (index == -1) {
            index = 0;
        }

        return keyFileContent.substring(0, index) + System.lineSeparator() + sb
                + keyFileContent.substring(index);
    }

    @Override
    public void setBootClassPath(@Nullable Path path) throws IllegalStateException {
        if (bootclasspath != null) {
            throw new IllegalStateException("Bootclasspath is already set!");
        }
        if (path != null) {
            bootclasspath = path.toAbsolutePath().normalize();
        }
    }

    @Override
    public void setClassPath(@Nullable List<Path> paths) throws IllegalStateException {
        if (classpath != null) {
            throw new IllegalStateException("Classpath is already set!");
        }
        if (paths != null) {
            classpath = paths.stream().filter(Objects::nonNull) // to be sure it contains no null
                                                                // elements
                                                                // convert Files to Paths and
                                                                // normalize
                    .map(p -> p.toAbsolutePath().normalize()).collect(Collectors.toList());
        }
    }

    @Override
    public void setJavaPath(@Nullable Path path) throws IllegalStateException {
        if (javaPath != null) {
            throw new IllegalStateException("JavaPath is already set!");
        }
        if (path != null) {
            javaPath = path.toAbsolutePath().normalize();
        }
    }

    @Override
    /**
     * Sets the base directory of this repository, reading in either the given directory or, for a
     * file, its containing directory.
     * <p>
     * A base path that is a file always has a containing directory; the dereference of the
     * (nullable) parent of the absolute path is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
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

    @Override
    public void registerProof(Proof proof) {
        registeredProofs.add(proof);
        // register the repo in the proof to listen to ProofDisposedEvents.
        proof.addProofDisposedListener(this);
    }

    /**
     * Clears all data in the FileRepo and marks it as disposed.
     * <p>
     * The file and proof sets are deliberately set to {@code null} although their fields are
     * non-null, so that all referenced objects become garbage-collectable; a disposed repo is never
     * used again, hence the null assignments are safe and suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:assignment.type.incompatible")
    protected void dispose() {
        if (disposed) {
            return;
        }

        // delete all references
        javaPath = null;
        classpath = null;
        bootclasspath = null;
        baseDir = null;

        files.clear();
        files = null;
        registeredProofs = null; // this set is already empty, else the repo must not be disposed

        disposed = true;
    }

    @Override
    public void proofDisposing(ProofDisposedEvent e) {}

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
