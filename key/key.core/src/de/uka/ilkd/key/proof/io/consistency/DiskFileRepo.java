package de.uka.ilkd.key.proof.io.consistency;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.nio.file.Paths;
import java.util.Comparator;
import java.util.HashMap;

import de.uka.ilkd.key.proof.io.RuleSourceFactory;

/**
 * This class uses a temporary directory as a store for the proof-relevant files.
 *
 * @author Wolfram Pfeifer
 */
public class DiskFileRepo extends AbstractFileRepo {
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
    }

    @Override
    public InputStream getInputStream(Path path) throws IOException {
        // ignore URL files (those are internal files shipped with KeY)
        if (isURLFile(path)) {
            return null; // TODO: do not return null here, but a useful InputStream
        }

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
    public OutputStream createOutputStream(Path path) throws IOException {

        // store the file inside the temporary directory (relative to tmp dir)
        Path absTarget = tmpDir.resolve(path);

        try {
            FileOutputStream fos = new FileOutputStream(absTarget.toFile());

            // store the path translation in map
            // -> do not do this, since exists no copy of the file except in repo
            // Path translation = baseDir.resolve(path);
            // map.put(translation, absTarget);
            files.add(path);
            return fos;
        } catch (FileNotFoundException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return null;
    }

    @Override
    public Path getSaveName(Path path) throws IOException {
        // the given path is:
        // 1. already absolute or
        // 2. relative to the base dir
        // assumption: a file with the given path has already been stored in the repo
        //              (via getFile() or createOutputStream())

        Path abs = path;
        if (!path.isAbsolute()) {
            abs = baseDir.resolve(path);
        }

        if (!Files.exists(abs)) {
            // no map lookup possible -> use given name
         // TODO: what if path is absolute here?
            return path;
        }

        // for lookup we need the real path
        final Path real = abs.toAbsolutePath().normalize(); // .toRealPath();
        Path repoPath = map.get(real);

        // as return value, we need the path relative to repo directory (tmpDir)
        Path rel = tmpDir.relativize(repoPath);

        return rel;
    }

    @Override
    public void dispose() {
        if (disposed) {
            return;
        }

        try {
            // delete the temporary directory with all contained files
            Files.walk(tmpDir)
                .sorted(Comparator.reverseOrder())
                .map(Path::toFile)
                .forEach(File::delete);
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        // set every hold reference to null
        tmpDir = null;
        map = null;
        files = null;
        super.dispose();
    }

    @Override
    protected InputStream getInputStreamInternal(Path p) throws FileNotFoundException {
        // convert given path to actual file path
        Path concrete = tmpDir.resolve(p);
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
        Path rel = containing.relativize(norm); //containing.toRealPath().relativize(norm);

        // compute the absolute target path of the file in repo
        Path absTarget = tmpDir.resolve(relTarget).resolve(rel);

        // copy the old file to target path
        createDirsAndCopy(norm, absTarget);

        // register in map and list (for lookup and saving)
        map.put(norm, absTarget);
        files.add(norm);

        // return the path of the copied file
        return absTarget;
    }

    private InputStream getJavaFileInputStream(Path javaFile) throws IOException {
        // assumes that javaFile is an actual *.java file, path has to be absolute and normalized

        Path newFile = null;

        // where is the file located in (src, classpath, bootclasspath)
        if (isInJavaPath(javaFile)) {                                               // src
            newFile = resolveAndCopy(javaFile, javaPath, Paths.get("src"));
        } else if (isInBootClassPath(javaFile)) {                                   // bootclasspath
            newFile = resolveAndCopy(javaFile, bootclasspath, Paths.get("bootclasspath"));
        } else if (classpath != null) {                                             // classpath
            // search for matching classpath in the list
            for (Path cp : classpath) {
                // TODO: how to deal with zips/jars?

                // convert to real path (else the check may be erroneous)
                Path realCP = cp; //.toRealPath();
                if (javaFile.startsWith(realCP)) {         // only consider directories in classpath
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
        files.add(keyFile);

        // return a FileInputStream to the copied file
        return new FileInputStream(absTarget.toFile());
    }

    private InputStream getZipFileInputStream(Path zipFile) throws IOException {
        // copy to classpath folder (zip/jar may only occur in classpath)
        Path newFile = resolveAndCopy(zipFile, zipFile.getParent(), Paths.get("classpath"));
        // TODO: do we really want a FileInputStream here?
        return new FileInputStream(newFile.toFile());
    }

    private InputStream getClassFileInputStream(Path classFile) {
        // TODO:
        return null;
    }

    private boolean isInternalFile(Path path) throws IOException {
        return isBuiltInRuleFile(path);     // TODO: add check for internal java files and URLs
    }

    private static boolean isURLFile(Path path) {
        return path.startsWith("file:/");
    }

    private static boolean isBuiltInRuleFile(Path file) throws IOException {
        // TODO: check for URL
        return file.normalize().startsWith(KEYPATH);
    }

    // TODO: move to IOUtil
    private static void createDirsAndCopy(Path source, Path target) throws IOException {
        Files.createDirectories(target.getParent());
        Files.copy(source, target);
    }

    // shortcut for debug output
    private static void out(String s) {
        System.out.println(s);
    }
}
