package de.uka.ilkd.key.proof.io.consistency;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.JarURLConnection;
import java.net.URL;
import java.net.URLDecoder;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.nio.file.Paths;
import java.util.Comparator;
import java.util.HashMap;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import de.uka.ilkd.key.settings.GeneralSettings;

/**
 * This class uses a temporary directory as a store for the proof-relevant files.
 *
 * @author Wolfram Pfeifer
 */
public final class DiskFileRepo extends AbstractFileRepo {
    /**
     * The path where KeY's built-in rules are stored.
     * Needed to prevent built-in rules from getting cached.
     */
    protected static final Path KEYPATH = RuleSourceFactory.fromDefaultLocation("").file().toPath();

    /**
     * This matcher matches *.java files.
     */
    private static final PathMatcher JAVA_MATCHER =
            FileSystems.getDefault().getPathMatcher("glob:**.java");

    /**
     * A matcher matches *.key and *.proof files.
     */
    private static final PathMatcher KEY_MATCHER =
            FileSystems.getDefault().getPathMatcher("glob:**.{key,proof}");

    /**
     * This matcher matches *.zip and *.jar files.
     */
    private static final PathMatcher ZIP_MATCHER =
            FileSystems.getDefault().getPathMatcher("glob:**.{zip,jar}");

    /**
     * This matcher matches *.class files.
     */
    private static final PathMatcher CLASS_MATCHER =
            FileSystems.getDefault().getPathMatcher("glob:**.class");

    /**
     * The temporary directory used as a cache.
     */
    private Path tmpDir;

    /**
     * Stores for each requested path the mapping to its concrete path in repo.
     * Key and value paths are absolute, and even more, they are real paths.
     */
    private HashMap<Path, Path> map = new HashMap<Path, Path>();

    /**
     * Initializes a new empty DiskFileRepo. This creates a new temporary directory.
     * @param proofName name of the proof (used in the naming of the temporary directory)
     * @throws IOException if an I/O error occurs, e.g. the user has not the right to create the
     *      new temporary directory
     */
    public DiskFileRepo(String proofName) throws IOException {
        tmpDir = Files.createTempDirectory(proofName);

        // hook for deleting tmpDir + content at program exit
        Runtime.getRuntime().addShutdownHook(new Thread() {
            public void run() {
                try {
                    // delete the temporary directory with all contained files
                    deleteDiskContent();
                } catch (IOException e) {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                }
            }
        });
    }

    @Override
    public InputStream getInputStream(Path path) throws IOException {

        // wrap path into URL for uniform treatment
        return getInputStream(path.toUri().toURL());

//        // ignore URL files (those are internal files shipped with KeY)
//        if (isURLFile(path)) {
//            return null; // TODO: do not return null here, but a useful InputStream?
//        }
//
//        return copyAndOpenInputStream(path);
    }

    @Override
    public InputStream getInputStream(RuleSource ruleSource) throws IOException {
        // wrap file of RuleSource into an URL
        out("getting InputStream of RuleSource file: " + ruleSource.file());

        // TODO: this fails if the file is a zip file: in this case, file starts with "file:/"
        //URL url = file.toURI().toURL();

        return getInputStream(ruleSource.url());
    }

    @Override
    public InputStream getInputStream(URL url) throws IOException {
        String protocol = url.getProtocol();
        out("---- getting InputStream of URL: " + url.toString());

        // currently, we support only two protocols: file and zip/jar
        if (protocol.equals("file")) {
            // url.getPath() may contain escaped characters -> we have to decode it
            String path = URLDecoder.decode(url.getPath(), "UTF-8");
            out("-------- getting InputStream of URL path: " + path);

            return copyAndOpenInputStream(Paths.get(path));
        } else if (protocol.equals("jar")) {        // TODO: zip?
            JarURLConnection juc = (JarURLConnection) url.openConnection();
            Path jarPath = Paths.get(juc.getJarFile().getName());

            // TODO: wrong number of slashes somewhere

            // copy the actual file, but return an InputStream to the concrete entry:
            // - copy file of URL to repo
            // - add file to repo map
            getInputStream(jarPath).close();  // TODO: add private method registerPath or similar

            // - return an InputStream to the copy
            Path jarCopy = map.get(jarPath);
            out("-------- path of copied jar is " + jarPath);

            // we have to create the URL as string:
            String entryStr = "jar:file:///" + jarCopy.toString() + "!/" + juc.getEntryName();
            URL entryURL = new URL(entryStr);

            // URL entryURL = new URL(jarCopy.toUri().toURL(), juc.getEntryName());
            out("-------- the URL of the entry in the copied jar is " + entryURL);
            return entryURL.openStream();
        } else {
            throw new IllegalArgumentException("This type of RuleSource is not supported!");
        }
    }

    private InputStream copyAndOpenInputStream(Path path) throws IOException {
        // this method assumes that the path exists and is a valid (w/o protocol part as in URL!)

        final Path norm = path.toAbsolutePath().normalize();

        // map lookup if the current path was already requested
        final Path p = map.get(norm);
        if (p != null) {
            return new FileInputStream(p.toFile());
        }

        // internal files are not copied to repo (but added to map for faster lookup)
        if (isInternalFile(norm)) {
            // generate map entry
            map.put(norm, norm);

            // directly return an InputStream to the file
            return new FileInputStream(norm.toFile());
        }

        if (JAVA_MATCHER.matches(norm)) {                                    // .java
            // copy to src/classpath/bootclasspath (depending on path)
            return getJavaFileInputStream(norm);
        } else if (KEY_MATCHER.matches(norm)) {                              // .key/.proof
            // copy to top level
            // adapt file references
            return getKeyFileInputStream(norm);
        } else if (ZIP_MATCHER.matches(norm)) {                              // .zip/.jar
            // extract to classpath folder (new folder with archive name)
            return getZipFileInputStream(norm);
        } else if (CLASS_MATCHER.matches(norm)) {                            // .class
            // copy to classpath
            return getClassFileInputStream(norm);
        } else {
            out("Error! Unsupported file extension: " + norm);
        }
        return null;
    }

    @Override
    public OutputStream createOutputStream(Path path) throws FileNotFoundException {

        if (path.isAbsolute()) {
            // programming error!
            throw new IllegalArgumentException("The path is not absolute: " + path);
        }

        // store the file inside the temporary directory (relative to tmp dir)
        Path absTarget = tmpDir.resolve(path);

        // store the path translation in map
        // -> do not do this, since exists no copy of the file except in repo
        // Path translation = baseDir.resolve(path);
        // map.put(translation, absTarget);
        addFile(path);

        return new FileOutputStream(absTarget.toFile());
    }

    @Override
    protected Path getSaveName(Path path) {
        /* assumption: a file with the given path has already been stored in the repo
         *              (via getInputStream() or createOutputStream()) */

        /* the given path is:
         * 1. absolute                      -> lookup translation in map, relativize to tmpDir
         * 2. relative to the base dir      -> nothing to do */

        if (path.isAbsolute()) {
            // lookup translation in map, make relative to tmpDir
            return tmpDir.relativize(map.get(path.normalize()));
        } else {
            // already relative to tmpDir
            return path;
        }
    }

    @Override
    protected void dispose() {
        if (isDisposed()) {
            return;
        }

        try {
            // delete the temporary directory with all contained files
            deleteDiskContent();
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        // set every held reference to null
        tmpDir = null;
        map = null;
        super.dispose();
    }

    @Override
    protected InputStream getInputStreamInternal(Path p) throws FileNotFoundException {
        Path concrete;
        if (p.isAbsolute()) {                   // p is absolute -> lookup in map
            concrete = map.get(p.normalize());
        } else {                                // p is relative -> interpret as relative to tmpDir
            concrete = tmpDir.resolve(p.normalize());
        }

        if (concrete == null) {
            return null;
        }

        // open new FileInputStream of the converted path
        return new FileInputStream(concrete.toFile());
    }

    // norm: absolute and normalized path of the requested file
    // containing: src, classpath, or bootclasspath folder containing norm (absolute and normalized)
    // target: src, classpath, or bootclasspath in repo (relative to repo base dir)
    private Path resolveAndCopy(Path norm, Path containing, Path relTarget) throws IOException {
        // compute relative path from containing to norm
        Path rel = containing.relativize(norm);

        // compute the absolute target path of the file in repo
        Path absTarget = tmpDir.resolve(relTarget).resolve(rel);

        // copy the old file to target path
        createDirsAndCopy(norm, absTarget);

        // register in map and list (for lookup and saving)
        map.put(norm, absTarget);
        addFile(norm);

        // return the path of the copied file
        return absTarget;
    }

    private InputStream getJavaFileInputStream(Path javaFile) throws IOException {
        // assumes that javaFile is an actual *.java file, path has to be absolute and normalized

        Path newFile = null;

        // where is the file located in (src, classpath, bootclasspath)
        if (isInJavaPath(javaFile)) {                                              // src
            newFile = resolveAndCopy(javaFile, getJavaPath(), Paths.get("src"));
        } else if (isInBootClassPath(javaFile)) {                                  // bootclasspath
            newFile = resolveAndCopy(javaFile, getBootclasspath(), Paths.get("bootclasspath"));
        } else if (getClasspath() != null) {                                       // classpath
            // search for matching classpath in the list
            for (Path cp : getClasspath()) {
                // TODO: how to deal with zips/jars?

                if (javaFile.startsWith(cp)) {         // only consider directories in classpath
                    // we found the file location, so copy it
                    newFile = resolveAndCopy(javaFile, cp, Paths.get("classpath"));
                    break;
                }
            }
        } else {
            out("Error! None of the paths is set.");
        }

        if (newFile != null) {
            return new FileInputStream(newFile.toFile());
        }

        return null;
    }

    private InputStream getKeyFileInputStream(Path keyFile) throws IOException {
        // compute the absolute target path (top level in repo)
        Path absTarget = tmpDir.resolve(keyFile.getFileName());

        // copy the key file to target path
        // IMPORTANT: Do not call adapteFileRefs here. This should be done when saving a repo.
        createDirsAndCopy(keyFile, absTarget);

        // register in map and list (for lookup and saving)
        map.put(keyFile, absTarget);
        addFile(keyFile);

        // return a FileInputStream to the copied file
        return new FileInputStream(absTarget.toFile());
    }

    private InputStream getZipFileInputStream(Path zipFile) throws IOException {
        // copy to classpath folder (zip/jar may only occur in classpath)
        Path newFile = resolveAndCopy(zipFile, zipFile.getParent(), Paths.get("classpath"));
        // TODO: do we really want a FileInputStream here?
        return new FileInputStream(newFile.toFile());
    }

    private InputStream getClassFileInputStream(Path classFile) throws IOException {
        // copy to classpath folder (*.class files may only occur in classpath)
        Path newFile = resolveAndCopy(classFile, classFile.getParent(), Paths.get("classpath"));
        return new FileInputStream(newFile.toFile());
    }

    /**
     * Deletes the temporary directory with all contents (if not already done).
     * @throws IOException if the directory or one of its files is not accessible
     */
    private void deleteDiskContent() throws IOException {
        if (!isDisposed() && !GeneralSettings.keepFileRepos) {
            Files.walk(tmpDir)
                 .sorted(Comparator.reverseOrder())
                 .map(Path::toFile)
                 .forEach(File::delete);
        }
    }

    private static boolean isInternalFile(Path path) {
        return path.normalize().startsWith(KEYPATH);
    }

    // TODO: move to IOUtil?
    private static void createDirsAndCopy(Path source, Path target) throws IOException {
        Files.createDirectories(target.getParent());
        Files.copy(source, target);
    }

    // shortcut for debug output
    private static void out(String s) {     // TODO: delete
        System.out.println(s);
    }
}

