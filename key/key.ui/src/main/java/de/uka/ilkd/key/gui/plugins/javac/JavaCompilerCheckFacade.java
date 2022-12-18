package de.uka.ilkd.key.gui.plugins.javac;

import de.uka.ilkd.key.gui.PositionedIssueString;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nonnull;
import javax.tools.DiagnosticCollector;
import javax.tools.JavaCompiler;
import javax.tools.JavaFileObject;
import javax.tools.ToolProvider;
import java.io.File;
import java.io.IOException;
import java.io.StringWriter;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Locale;
import java.util.concurrent.CompletableFuture;
import java.util.stream.Collectors;
import java.util.stream.Stream;

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
     *        about any
     *        issues found in the target Java program
     * @param bootClassPath the {@link File} referring to the path containing the core Java classes
     * @param classpath the {@link List} of {@link File}s referring to the directory that make up
     *        the target Java programs classpath
     * @param sourcepath the {@link String} with the path to the source of the target Java program
     * @return
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

        var fileManager = compiler.getStandardFileManager(
            diagnostics, Locale.ENGLISH, Charset.defaultCharset());

        var output = new StringWriter();
        var classes = new ArrayList<String>();

        var paths = new ArrayList<File>();
        if (bootClassPath != null) {
            paths.add(bootClassPath);
        }
        if (classPath != null && !classPath.isEmpty()) {
            paths.addAll(classPath);
        }
        paths.add(javaPath);
        var compilationUnits =
            fileManager.getJavaFileObjects(paths.stream()
                    .filter(File::isDirectory)
                    .flatMap(it -> {
                        try {
                            return Files.walk(it.toPath())
                                    .filter(f -> !Files.isDirectory(f))
                                    .filter(f -> f.getFileName().toString().endsWith(".java"));
                        } catch (IOException e) {
                            LOGGER.info("", e);
                            return Stream.empty();
                        }
                    }).toArray(Path[]::new));

        var task = compiler.getTask(output, fileManager, diagnostics,
            new ArrayList<>(), classes, compilationUnits);

        return CompletableFuture.supplyAsync(() -> {
            long start = System.currentTimeMillis();
            var b = task.call();
            LOGGER.info("Javac check took {} ms.", System.currentTimeMillis() - start);
            for (var diagnostic : diagnostics.getDiagnostics()) {
                LOGGER.info("{}", diagnostic);
            }
            return diagnostics.getDiagnostics().stream().map(
                it -> new PositionedIssueString(
                    it.getMessage(Locale.ENGLISH),
                    fileManager.asPath(it.getSource()).toFile().getAbsolutePath(),
                    new Position((int) it.getLineNumber(), (int) it.getColumnNumber()),
                    "" + it.getCode() + " " + it.getKind()))
                    .collect(Collectors.toList());
        });
    }
}
