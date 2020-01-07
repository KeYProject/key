package org.key_project.proofmanagement.io;

import java.io.IOException;
import java.nio.file.*;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.key_project.proofmanagement.check.PathNode;
import org.key_project.util.java.IOUtil;


/**
 * This class serves as an extractor to get the paths of specific files inside a proof bundle
 * (a zip containing possibly multiple *.proof/*.key files and corresponding source/classpath
 * files in a well defined directory structure).
 */
public class ProofBundleHandler {
    /**
     * A matcher matches *.proof files.
     */
    private static final PathMatcher PROOF_MATCHER =
            FileSystems.getDefault().getPathMatcher("glob:**.proof");

    /**
     * A matcher matches *.key files.
     */
    private static final PathMatcher KEY_MATCHER =
            FileSystems.getDefault().getPathMatcher("glob:**.key");

    /**
     * This matcher matches *.java files.
     */
    private static final PathMatcher SRC_MATCHER =
            FileSystems.getDefault().getPathMatcher("glob:**.java");

    /**
     * This matcher matches *.java, *.class, *.zip, and *.jar files.
     */
    private static final PathMatcher CLASSPATH_MATCHER =
            FileSystems.getDefault().getPathMatcher("glob:**.{java,class,zip,jar}");

    /**
     * This matcher matches *.java files.
     */
    private static final PathMatcher BOOTCLASSPATH_MATCHER =
            FileSystems.getDefault().getPathMatcher("glob:**.java");

    private Path zipPath;
    private boolean isInitialized = false;
    private Path tmpDir;

    /**
     * Creates a new PackageHandler for the specified proof bundle.
     * @param zipPath the path of the proof bundle (zip file)
     */
    public ProofBundleHandler(Path zipPath) {
        this.zipPath = zipPath;
    }

    private void load() throws IOException {
        if (!isInitialized) {
            tmpDir = Files.createTempDirectory("KeY_PM_unzip");
            IOUtil.extractZip(zipPath, tmpDir);

            isInitialized = true;
        }
    }

    // IMPORTANT: get... methods return paths to unzipped files!

    private List<Path> getFiles(Path dir, PathMatcher matcher) throws IOException {
        List<Path> files = new ArrayList<>();
        if (Files.isDirectory(dir)) {
            // IMPORTANT: use try-with-resources here to ensure the stream is closed and does not
            //  prevent the files from deletion on Windows!
            try (Stream<Path> stream = Files.list(dir)) {
                files.addAll(stream.filter(matcher::matches)
                                   .collect(Collectors.toList()));
            }
        }
        return files;
    }

    // *.proof
    public List<Path> getProofFiles() throws IOException {
        // ensure the zip is extracted
        load();

        return getFiles(tmpDir, PROOF_MATCHER);
    }

    // *.key
    public List<Path> getKeYFiles() throws IOException {
        // ensure the zip is extracted
        load();

        return getFiles(tmpDir, KEY_MATCHER);
    }

    // *.java
    public List<Path> getSourceFiles() throws IOException {
        // ensure the zip is extracted
        load();

        Path srcPath = tmpDir.resolve(Paths.get("src"));
        return getFiles(srcPath, SRC_MATCHER);
    }

    // *.java, *.class, *.zip, *.jar
    public List<Path> getClasspathFiles() throws IOException {
        // ensure the zip is extracted
        load();

        Path classpathPath = tmpDir.resolve(Paths.get("classpath"));
        return getFiles(classpathPath, CLASSPATH_MATCHER);
    }

    // *.java
    public List<Path> getBootclasspathFiles() throws IOException {
        // ensure the zip is extracted
        load();

        Path bootclasspathPath = tmpDir.resolve(Paths.get("bootclasspath"));
        return getFiles(bootclasspathPath, BOOTCLASSPATH_MATCHER);
    }

    public Path getDir() {
        return tmpDir;
    }

    /**
     * Deletes temporary content from disk.
     */
    public void dispose() {
        try {
            Files.walk(tmpDir)
                    .sorted(Comparator.reverseOrder())
                    .forEach(
                        p -> {
                            try {
                                Files.delete(p);
                            } catch (IOException e) {
                                e.printStackTrace();
                            }
                        });
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private static class TreeFileVisitor extends SimpleFileVisitor<Path> {

        PathNode start;
        PathNode current;

        public TreeFileVisitor(PathNode start) {
            this.start = start;
            this.current = start;
        }

        @Override
        public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) throws IOException {
            PathNode node = new PathNode(current, dir);
            current.addChild(node);
            current = node;
            return FileVisitResult.CONTINUE;
        }

        @Override
        public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
            PathNode node = new PathNode(current, file);
            current.addChild(node);
            return FileVisitResult.CONTINUE;
        }

        @Override
        public FileVisitResult postVisitDirectory(Path dir, IOException exc) throws IOException {
            current = current.getParent();
            return FileVisitResult.CONTINUE;
        }
    }

    public PathNode getFileTree() throws IOException {
        load();

        PathNode root = new PathNode(null, tmpDir);
        Files.walkFileTree(tmpDir, new TreeFileVisitor(root));
        // prevent double inclusion of root directory itself
        // TODO: check why this is necessary
        return (PathNode) root.getChildren().first();
    }
}
