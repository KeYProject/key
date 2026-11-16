/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.io;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.catchThrowable;

/**
 * Reproducer for the unsupported-construct defects fixed in #4038.
 * <p>
 * These tests are <b>expected to fail on main</b>: KeY's JML/Java translation crashes with a
 * {@code NullPointerException} or {@code ClassCastException} instead of reporting a structured
 * diagnostic of the form {@code <file>:<line>:<col>: construct '<snippet>' not supported:
 * <reason>} (§8 of the headless interface spec). They only reference the diagnostic text (not
 * the exception type added by #4038), so that the same test compiles and passes once #4038 is
 * merged.
 */
class UnsupportedConstructReproTest {

    /** {@code assignable bucketData[*][*];} in a method contract (defect in the JML translator). */
    private static final String STAR_STAR = "public class Bad {\n"
        + "    public int[][] bucketData;\n"
        + "\n"
        + "    /*@ public normal_behavior\n"
        + "      @   assignable bucketData[*][*];\n"
        + "      @   ensures true;\n"
        + "      @*/\n"
        + "    public void set() {\n"
        + "    }\n"
        + "}\n";

    /** {@code int[][] a = new int[n][];}, an array creation with an unsized dimension. */
    private static final String UNSIZED_DIMENSION = "public class Bad {\n"
        + "    /*@ public normal_behavior\n"
        + "      @   ensures true;\n"
        + "      @*/\n"
        + "    public int m(int n) {\n"
        + "        int[][] a = new int[n][];\n"
        + "        return 0;\n"
        + "    }\n"
        + "}\n";

    /** {@code int[][] a = new int[][]{{1,2}};}, a nested array initializer. */
    private static final String NESTED_INITIALIZER = "public class Bad {\n"
        + "    /*@ public normal_behavior\n"
        + "      @   ensures true;\n"
        + "      @*/\n"
        + "    public int m() {\n"
        + "        int[][] a = new int[][]{{1,2}};\n"
        + "        return 0;\n"
        + "    }\n"
        + "}\n";

    @Test
    void nestedStarReferenceIsReportedAsUnsupportedConstruct() throws IOException {
        Throwable failure = loadFailure("star", STAR_STAR);

        assertThat(messagesOf(failure))
                .as("expected the §8 diagnostic, but main crashed with: %s", describe(failure))
                .containsPattern("Bad\\.java:5:22: construct 'bucketData\\[\\*\\]\\[\\*\\]' "
                    + "not supported: ");
    }

    @Test
    void unsizedArrayDimensionIsReportedAsUnsupportedConstruct() throws IOException {
        Throwable failure = loadFailure("unsized", UNSIZED_DIMENSION);

        assertThat(messagesOf(failure))
                .as("expected the §8 diagnostic, but main crashed with: %s", describe(failure))
                .containsPattern(
                    "Bad\\.java:6:21: construct 'new int\\[n\\]\\[\\]' not supported: ");
    }

    @Test
    void nestedArrayInitializerIsReportedAsUnsupportedConstruct() throws IOException {
        Throwable failure = loadFailure("initializer", NESTED_INITIALIZER);

        assertThat(messagesOf(failure))
                .as("expected the §8 diagnostic, but main crashed with: %s", describe(failure))
                .containsPattern(
                    "Bad\\.java:6:21: construct 'new int\\[\\]\\[\\]\\{\\{1,2\\}\\}' not supported: ");
    }

    /**
     * Writes the given Java source plus a minimal load file into a fresh directory and returns the
     * exception that loading the file throws.
     */
    private static Throwable loadFailure(String name, String javaSource) throws IOException {
        Path dir = Files.createTempDirectory("unsupported-construct-" + name);
        Files.writeString(dir.resolve("Bad.java"), javaSource);
        Path key = dir.resolve("index.key");
        Files.writeString(key,
            "\\profile \"Java Profile\";\n\n\\javaSource \".\";\n\n\\problem { true }\n");

        Throwable thrown = catchThrowable(() -> KeYEnvironment.load(key));
        assertThat(thrown).as("loading %s must fail", key).isNotNull();
        return thrown;
    }

    /** All non-null messages of the given exception chain, separated by newlines. */
    private static String messagesOf(Throwable thrown) {
        StringBuilder messages = new StringBuilder();
        for (Throwable t = thrown; t != null; t = t.getCause()) {
            if (t.getMessage() != null) {
                messages.append(t.getMessage()).append('\n');
            }
        }
        return messages.toString();
    }

    /** The exception chain as {@code ClassName: message | ClassName: message | ...}. */
    private static String describe(Throwable thrown) {
        StringBuilder description = new StringBuilder();
        for (Throwable t = thrown; t != null; t = t.getCause()) {
            if (description.length() > 0) {
                description.append(" | ");
            }
            description.append(t.getClass().getSimpleName());
            if (t.getMessage() != null) {
                String message = t.getMessage().replace('\n', ' ');
                description.append(": ").append(message);
            }
        }
        return description.toString();
    }
}
