/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.javac;

import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.io.StringWriter;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.concurrent.CompletableFuture;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;
import javax.tools.*;

import de.uka.ilkd.key.gui.PositionedIssueString;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.init.ProblemInitializer;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This facade checks whether the Java program to be verified is compilable using <code>javac</code>
 * via
 * the {@link JavaCompiler} class .
 * <p>
 * For setting up <code>javac</code> it uses the KeY project information about the bootpath and
 * classpath.
 * Any issues found in the compilation are reported to a provided listener of type
 * {@link ProblemInitializer.ProblemInitializerListener}.
 * <p>
 * Checking the target Java code can be enabled / disabled by providing the property
 * <code>-PKEY_JAVAC_DISABLE=true</code> / <code>-PKEY_JAVAC_DISABLE=false</code> on startup of KeY.
 *
 * @author Alexander Weigl
 * @version 1 (14.10.22)
 */
public class JavaCompilerCheckFacade {
    private static final Logger LOGGER = LoggerFactory.getLogger(JavaCompilerCheckFacade.class);

    /**
     * initiates the compilation check on the target Java source (the Java program to be verified)
     * and
     * reports any issues to the provided <code>listener</code>
     *
     * @param listener the {@link ProblemInitializer.ProblemInitializerListener} to be informed
     *        about any issues found in the target Java program
     * @param bootClassPath the {@link File} referring to the path containing the core Java classes
     * @param classPath the {@link List} of {@link File}s referring to the directory that make up
     *        the target Java programs classpath
     * @param javaPath the {@link String} with the path to the source of the target Java program
     * @return future providing the list of diagnostics
     */
    @Nonnull
    public static CompletableFuture<List<PositionedIssueString>> check(
            ProblemInitializer.ProblemInitializerListener listener,
            File bootClassPath, List<File> classPath, File javaPath) {
        if (Boolean.getBoolean("KEY_JAVAC_DISABLE")) {
            LOGGER.info("Javac check is disabled by system property -PKEY_JAVAC_DISABLE");
            return CompletableFuture.completedFuture(Collections.emptyList());
        }
        LOGGER.info("Javac check is triggered. To disable use property -PKEY_JAVAC_DISABLE=true");

        DiagnosticCollector<JavaFileObject> diagnostics = new DiagnosticCollector<>();
        JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();

        if (compiler == null) {
            LOGGER.info("Javac is not available in current java runtime. Javac check skipped");
            listener.reportStatus(null, "No javac compiler found. Java check disabled.");
            return CompletableFuture.completedFuture(Collections.emptyList());
        }

        JavaFileManagerDelegate fileManager =
            new JavaFileManagerDelegate(
                compiler.getStandardFileManager(
                    diagnostics, Locale.ENGLISH, Charset.defaultCharset()));

        StringWriter output = new StringWriter();
        List<String> classes = new ArrayList<>();

        // gather configured bootstrap classpath and regular classpath
        List<File> paths = new ArrayList<>();
        if (bootClassPath != null) {
            paths.add(bootClassPath);
        }
        if (classPath != null && !classPath.isEmpty()) {
            paths.addAll(classPath);
        }
        paths.add(javaPath);
        ArrayList<Path> files = new ArrayList<>();
        for (File path : paths) {
            if (!path.isDirectory()) {
                continue;
            }
            try (var s = Files.walk(path.toPath())) {
                s.filter(f -> !Files.isDirectory(f))
                        .filter(f -> f.getFileName().toString().endsWith(".java"))
                        .forEachOrdered(files::add);
            } catch (IOException e) {
                LOGGER.info("", e);
            }
        }
        Iterable<? extends JavaFileObject> compilationUnits =
            fileManager.getJavaFileObjects(files.toArray(new Path[0]));

        JavaCompiler.CompilationTask task = compiler.getTask(output, fileManager, diagnostics,
            new ArrayList<>(), classes, compilationUnits);

        return CompletableFuture.supplyAsync(() -> {
            long start = System.currentTimeMillis();
            var b = task.call();
            LOGGER.info("Javac check took {} ms.", System.currentTimeMillis() - start);
            for (Diagnostic<? extends JavaFileObject> diagnostic : diagnostics.getDiagnostics()) {
                LOGGER.info("{}", diagnostic);
            }
            return diagnostics.getDiagnostics().stream().map(
                it -> new PositionedIssueString(
                    it.getMessage(Locale.ENGLISH),
                    new Location(
                        fileManager.asPath(it.getSource()).toFile().toPath().toUri(),
                        Position.newOneBased((int) it.getLineNumber(),
                            (int) it.getColumnNumber())),
                    it.getCode() + " " + it.getKind()))
                    .collect(Collectors.toList());
        });
    }
}


/**
 * Wrapper around a {@link StandardJavaFileManager} that returns a dummy output for
 * class files ({@link #getJavaFileForOutput(Location, String, JavaFileObject.Kind, FileObject)}.
 * Every other request is delegated to the provided file manager.
 *
 * @author Alexander Weigl
 */
class JavaFileManagerDelegate implements StandardJavaFileManager {
    /**
     * The file manager most calls are delegated to.
     */
    private final StandardJavaFileManager fileManager;

    /**
     * Construct a new wrapper.
     *
     * @param jfm file manager
     */
    public JavaFileManagerDelegate(StandardJavaFileManager jfm) {
        this.fileManager = jfm;
    }

    @Override
    public boolean isSameFile(FileObject a, FileObject b) {
        return fileManager.isSameFile(a, b);
    }

    @Override
    public Iterable<? extends JavaFileObject> getJavaFileObjectsFromFiles(
            Iterable<? extends File> files) {
        return fileManager.getJavaFileObjectsFromFiles(files);
    }


    @Override
    @Deprecated(since = "13")
    public Iterable<? extends JavaFileObject> getJavaFileObjectsFromPaths(
            Iterable<? extends Path> paths) {
        return fileManager.getJavaFileObjectsFromPaths(paths);
    }

    @Override
    public Iterable<? extends JavaFileObject> getJavaFileObjects(File... files) {
        return fileManager.getJavaFileObjects(files);
    }

    @Override
    public Iterable<? extends JavaFileObject> getJavaFileObjects(Path... paths) {
        return fileManager.getJavaFileObjects(paths);
    }

    @Override
    public Iterable<? extends JavaFileObject> getJavaFileObjectsFromStrings(
            Iterable<String> names) {
        return fileManager.getJavaFileObjectsFromStrings(names);
    }

    @Override
    public Iterable<? extends JavaFileObject> getJavaFileObjects(String... names) {
        return fileManager.getJavaFileObjects(names);
    }

    @Override
    public void setLocation(Location location, Iterable<? extends File> files) throws IOException {
        fileManager.setLocation(location, files);
    }

    @Override
    public void setLocationFromPaths(Location location, Collection<? extends Path> paths)
            throws IOException {
        fileManager.setLocationFromPaths(location, paths);
    }

    @Override
    public void setLocationForModule(Location location, String moduleName,
            Collection<? extends Path> paths) throws IOException {
        fileManager.setLocationForModule(location, moduleName, paths);
    }

    @Override
    public Iterable<? extends File> getLocation(Location location) {
        return fileManager.getLocation(location);
    }

    @Override
    public Iterable<? extends Path> getLocationAsPaths(Location location) {
        return fileManager.getLocationAsPaths(location);
    }

    @Override
    public Path asPath(FileObject file) {
        return fileManager.asPath(file);
    }

    @Override
    public void setPathFactory(PathFactory f) {
        fileManager.setPathFactory(f);
    }

    @Override
    public ClassLoader getClassLoader(Location location) {
        return fileManager.getClassLoader(location);
    }

    @Override
    public Iterable<JavaFileObject> list(Location location, String packageName,
            Set<JavaFileObject.Kind> kinds, boolean recurse) throws IOException {
        return fileManager.list(location, packageName, kinds, recurse);
    }

    @Override
    public String inferBinaryName(Location location, JavaFileObject file) {
        return fileManager.inferBinaryName(location, file);
    }

    @Override
    public boolean handleOption(String current, Iterator<String> remaining) {
        return fileManager.handleOption(current, remaining);
    }

    @Override
    public boolean hasLocation(Location location) {
        return fileManager.hasLocation(location);
    }

    @Override
    public JavaFileObject getJavaFileForInput(Location location, String className,
            JavaFileObject.Kind kind) throws IOException {
        return fileManager.getJavaFileForInput(location, className, kind);
    }

    @Override
    public JavaFileObject getJavaFileForOutput(Location location, String className,
            JavaFileObject.Kind kind, FileObject sibling) throws IOException {
        if (kind == JavaFileObject.Kind.CLASS && location == StandardLocation.CLASS_OUTPUT) {
            // do not save compiled .class files on disk
            try {
                return new IgnoreOutputJavaFileObject(className, kind);
            } catch (URISyntaxException e) {
                throw new RuntimeException(e);
            }
        }
        return fileManager.getJavaFileForOutput(location, className, kind, sibling);
    }


    @Override
    public FileObject getFileForInput(Location location, String packageName, String relativeName)
            throws IOException {
        return fileManager.getFileForInput(location, packageName, relativeName);
    }

    @Override
    public FileObject getFileForOutput(Location location, String packageName, String relativeName,
            FileObject sibling) throws IOException {
        return fileManager.getFileForOutput(location, packageName, relativeName, sibling);
    }


    @Override
    public void flush() throws IOException {
        fileManager.flush();
    }

    @Override
    public void close() throws IOException {
        fileManager.close();
    }

    @Override
    public Location getLocationForModule(Location location, String moduleName) throws IOException {
        return fileManager.getLocationForModule(location, moduleName);
    }

    @Override
    public Location getLocationForModule(Location location, JavaFileObject fo) throws IOException {
        return fileManager.getLocationForModule(location, fo);
    }

    @Override
    public <S> ServiceLoader<S> getServiceLoader(Location location, Class<S> service)
            throws IOException {
        return fileManager.getServiceLoader(location, service);
    }

    @Override
    public String inferModuleName(Location location) throws IOException {
        return fileManager.inferModuleName(location);
    }

    @Override
    public Iterable<Set<Location>> listLocationsForModules(Location location) throws IOException {
        return fileManager.listLocationsForModules(location);
    }

    @Override
    public boolean contains(Location location, FileObject fo) throws IOException {
        return fileManager.contains(location, fo);
    }

    @Override
    public int isSupportedOption(String option) {
        return fileManager.isSupportedOption(option);
    }
}


/**
 * Java file object that ignores all writes.
 *
 * @author Alexander Weigl
 */
class IgnoreOutputJavaFileObject extends SimpleJavaFileObject {
    public IgnoreOutputJavaFileObject(final String name, Kind kind) throws URISyntaxException {
        super(new URI("memory://" + name + ".class"), kind);
    }

    // ignore written class output
    @Override
    public OutputStream openOutputStream() {
        return OutputStream.nullOutputStream();
    }
}
