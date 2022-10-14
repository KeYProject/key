package de.uka.ilkd.key.javac;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.expression.operator.LogicalOr;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.speclang.PositionedString;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.tools.*;
import java.io.File;
import java.io.IOException;
import java.io.StringWriter;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.concurrent.ForkJoinPool;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (14.10.22)
 */
public class JavaCompilerCheckFacade {
    private static final Logger LOGGER = LoggerFactory.getLogger(JavaCompilerCheckFacade.class);

    public static void check(ProblemInitializer.ProblemInitializerListener listener,
                             File bootClassPath, List<File> classPath, String javaPath) {
        if (Boolean.getBoolean("KEY_JAVAC_DISABLE")) {
            LOGGER.info("Javac check is disabled by system property -PKEY_JAVAC_DISABLE");
            return;
        }
        LOGGER.info("Javac check is triggered. To disable use property -PKEY_JAVAC_DISABLE=true");

        DiagnosticCollector<JavaFileObject> diagnostics = new DiagnosticCollector<>();
        JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();

        if (compiler == null) {
            LOGGER.info("Javac is not available in current java runtime. Javac check skipped");
            listener.reportStatus(null, "No javac compiler found. Java check disabled.");
            return;
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
        paths.add(new File(javaPath));
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
        ForkJoinPool.commonPool().submit(() -> {
            long start = System.currentTimeMillis();
            var b = task.call();
            LOGGER.info("Javac check took {} ms.", System.currentTimeMillis() - start);
            for (var diagnostic : diagnostics.getDiagnostics()) {
                LOGGER.info("{}", diagnostic);
            }
            if (!diagnostics.getDiagnostics().isEmpty()) {
                listener.showIssueDialog(
                        diagnostics.getDiagnostics().stream().map(
                                        it -> new PositionedString(it.getMessage(Locale.ENGLISH),
                                                fileManager.asPath(it.getSource()).toFile().getAbsolutePath(),
                                                new Position((int) it.getLineNumber(),
                                                        (int) it.getColumnNumber())))
                                .collect(Collectors.toList())

                );
            }
        });
    }
}
