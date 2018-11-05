package de.uka.ilkd.key.proof.io.consistency;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.file.FileSystem;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
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
     * The temporary directory used as a cache.
     */
    private Path tmpDir;

    /**
     * Stores for each requested path the mapping to its concrete path in temp dir.
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

    // TODO: care about links
    @Override
    public InputStream getFile(Path path) throws FileNotFoundException, IOException {
        System.out.println("getFile() -> path: " + path);
        final Path norm = path.toAbsolutePath().normalize();

        final Path p = map.get(norm);
        System.out.println("    norm: " + norm + "\n    p: " + p);
        if (p != null) {                             // already in map -> everything already done
            System.out.println("    Already existing: " + p);
            return new FileInputStream(p.toFile());
        } else {                                     // create new temp file
            // where is the file?
            // .java files: (javapath, classpath, bootclasspath)
            // .proof/.key files
            FileSystem fs = FileSystems.getDefault();
            if (fs.getPathMatcher("glob:**.java").matches(norm)) {                // *.java
                if (javaPath != null && norm.startsWith(javaPath)) {
                    Path srcDir = tmpDir.resolve(Paths.get("src"));
                    final Path rel = javaPath.relativize(norm);
                    System.out.println("    rel: " + rel);
                    System.out.println("    srcDir: " + srcDir);

                    Path newFile = srcDir.resolve(rel);

                    if (!Files.exists(newFile.getParent())) {   // create parent dir if not existing
                        Files.createDirectories(newFile.getParent());
                    }

                    System.out.println("    Copying " + norm + " to " + newFile);
                    Files.copy(norm, newFile);

                    System.out.println("    Put to map: key: " + norm.getFileName()
                        + " val: " + newFile);
                    map.put(norm, newFile);
                    files.add(Paths.get("src").resolve(rel));

                    return new FileInputStream(newFile.toFile());
                } else if (classPath != null && norm.startsWith(classPath)) {
                    System.out.println("Not yet implemented: CP");
                } else if (bootClassPath != null && norm.startsWith(bootClassPath)) {
                    System.out.println("Not yet implemented: BCP");
                } else {
                    // TODO: should not happen
                    System.out.println("Should not happen");
                }
            } else if (fs.getPathMatcher("glob:**.{key,proof}").matches(norm)) {  //.key/.proof
                Path newFile;
                final Path rel;
                if (isBuiltInRuleFile(norm) || baseDir == null) {            // don't cache
                    System.out.println("        internal rule file (don't cache)!");
                    map.put(path, path);
                    return new FileInputStream(path.toFile());    // InputStream from original file!
                }

                rel = baseDir.relativize(norm);
                newFile = tmpDir.resolve(rel);

                System.out.println("Copying " + norm + " to " + newFile);
                if (!Files.exists(newFile.getParent())) {
                    Files.createDirectories(newFile.getParent());
                }
                Files.copy(norm, newFile);
                map.put(norm, newFile);
                files.add(rel);

                //files.add(new Source(newFile, new FileInputStream(newFile.toFile())));
                return new FileInputStream(newFile.toFile());    // TODO: many streams to same file?
            }
        }
        return null;
    }


    @Override
    public OutputStream createOutputStream(Path path) {
        // store the file inside the temporary directory
        Path output = tmpDir.resolve(path);

        try {
            FileOutputStream fos = new FileOutputStream(output.toFile());
            files.add(path);
            return fos;
        } catch (FileNotFoundException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return null;
    }

    private static boolean isBuiltInRuleFile(Path file) {
        // TODO: check for URL
        return file.normalize().startsWith(KEYPATH);
    }

    @Override
    public void dispose() {
        if (disposed) {
            return;
        }

        try {
            // delete the temporary directory with all contained files
            Files.walk(baseDir)
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
    public InputStream getInputStream(Path p) {
        // convert given path to actual file path
        Path concrete = tmpDir.resolve(p);
        if (concrete == null) {
            return null;
        }

        // open new FileInputStream of the converted path
        try {
            return new FileInputStream(concrete.toFile());
        } catch (FileNotFoundException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return null;
    }
}
