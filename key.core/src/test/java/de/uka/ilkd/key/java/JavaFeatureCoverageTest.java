/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.io.IOException;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.util.ExceptionTools;

import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

import static org.junit.jupiter.api.Assertions.fail;

/**
 * Pins down which Java language features KeY's front-end
 * ({@link de.uka.ilkd.key.java.loader.JP2KeYConverter} and the transformation pipeline) currently
 * accepts. This backs the "Java Coverage" support table in the user documentation.
 * <p>
 * The examples live under {@code src/test/resources/de/uka/ilkd/key/java/coverage} in two folders:
 * <ul>
 * <li>{@code supported/} — one directory per feature that KeY <em>parses</em> today. Each is loaded
 * and must keep loading; a failure here is a parser regression.</li>
 * <li>{@code rejected/} — one directory per feature that KeY does <em>not</em> parse today (it
 * throws at load time, usually "Unsupported element detected given by Java Parser"). Each must keep
 * being rejected; if one starts loading, the feature has become supported and the test (plus the
 * documentation table) must be updated.</li>
 * </ul>
 * Every example also compiles with {@code javac} 21, so a load failure reflects KeY's front-end and
 * not malformed Java. Note this checks <em>parseability</em>, not sound reasoning: a few
 * {@code supported/} features (e.g. autoboxing, try-with-resources) load but are not soundly
 * modelled, as noted in the documentation.
 *
 * @see de.uka.ilkd.key.java.loader.JP2KeYConverter
 */
public class JavaFeatureCoverageTest {

    /** Each directory here must keep parsing; a throw is a front-end regression. */
    @TestFactory
    public Stream<DynamicTest> supportedFeaturesStayParseable() throws Exception {
        return featureDirs("supported")
                .map(dir -> DynamicTest.dynamicTest(dir.getFileName().toString(),
                    () -> {
                        Throwable error = tryLoad(dir);
                        if (error != null) {
                            fail("Regression: the Java feature '" + dir.getFileName()
                                + "' no longer parses, although it is listed as supported. "
                                + "If dropping it is intended, move it to 'coverage/rejected/' and update "
                                + "the Java Coverage documentation table. Load error: "
                                + firstMessage(error));
                        }
                    }));
    }

    /**
     * Each directory here must keep being rejected. If one starts to parse, the feature is now
     * supported and both this test and the documentation must be updated.
     */
    @TestFactory
    public Stream<DynamicTest> unsupportedFeaturesStayRejected() throws Exception {
        return featureDirs("rejected")
                .map(dir -> DynamicTest.dynamicTest(dir.getFileName().toString(),
                    () -> {
                        Throwable error = tryLoad(dir);
                        if (error == null) {
                            fail("'" + dir.getFileName()
                                + "' is now supported and the test should be "
                                + "modified to reflect the new addition: move it from 'coverage/rejected/' "
                                + "to 'coverage/supported/' and update the Java Coverage documentation "
                                + "table (mark the feature as supported).");
                        }
                    }));
    }

    // --- helpers -----------------------------------------------------------------------------

    private static Stream<Path> featureDirs(String kind) throws IOException, URISyntaxException {
        Path base = coverageRoot().resolve(kind);
        Assumptions.assumeTrue(Files.isDirectory(base),
            "coverage examples not found at " + base.toAbsolutePath());
        try (Stream<Path> s = Files.list(base)) {
            // Materialise so the directory stream is closed before the dynamic tests run.
            List<Path> dirs = s.filter(Files::isDirectory).sorted().collect(Collectors.toList());
            return dirs.stream();
        }
    }

    private static Path coverageRoot() throws URISyntaxException {
        // Prefer the copied test resources on the classpath (location-independent),
        // fall back to the module-relative source path.
        var url = JavaFeatureCoverageTest.class.getResource("/de/uka/ilkd/key/java/coverage");
        if (url != null) {
            return Paths.get(url.toURI());
        }
        return Paths.get("src/test/resources/de/uka/ilkd/key/java/coverage");
    }

    /** Loads the feature's {@code problem.key}; returns {@code null} on success, else the error. */
    private static Throwable tryLoad(Path featureDir) {
        Path problem = featureDir.resolve("problem.key");
        KeYEnvironment<?> env = null;
        try {
            env = KeYEnvironment.load(problem);
            return null;
        } catch (Throwable t) {
            return t;
        } finally {
            if (env != null) {
                try {
                    env.dispose();
                } catch (Throwable ignore) {
                }
            }
        }
    }

    private static String firstMessage(Throwable t) {
        List<String> msgs = new ArrayList<>();
        try {
            for (PositionedString ps : ExceptionTools.getMessages(t)) {
                msgs.add(ps.getText());
            }
        } catch (Throwable ignore) {
        }
        String joined = String.join(" | ", msgs);
        if (joined.isBlank()) {
            joined = t.getClass().getSimpleName()
                    + (t.getMessage() != null ? ": " + t.getMessage() : "");
        }
        return joined.replaceAll("\\s+", " ").trim();
    }
}
