/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.io;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.IdentityHashMap;
import java.util.Set;

import de.uka.ilkd.key.control.KeYEnvironment;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * Regression test for the §8 diagnostic contract: the three constructs that used to crash KeY's
 * JML/Java translation with a {@code NullPointerException} or {@code ClassCastException}
 * (during problem loading) must instead fail the load with a structured
 * {@link ConstructNotSupportedException} carrying the exact source snippet and the 1-based
 * line/column of the construct.
 */
class ConstructNotSupportedExceptionTest {

    /** {@code assignable bucketData[*][*];} in a method contract (bad construct 1). */
    private static final String BAD_STAR = "public class Bad {\n"
        + "    public int[][] bucketData;\n"
        + "\n"
        + "    /*@ public normal_behavior\n"
        + "      @   assignable bucketData[*][*];\n"
        + "      @   ensures true;\n"
        + "      @*/\n"
        + "    public void set() {\n"
        + "    }\n"
        + "}\n";

    /** {@code int[][] a = new int[n][];}, an unsized array creation (bad construct 2). */
    private static final String BAD_UNSIZED = "public class Bad {\n"
        + "    /*@ public normal_behavior\n"
        + "      @   ensures true;\n"
        + "      @*/\n"
        + "    public int m(int n) {\n"
        + "        int[][] a = new int[n][];\n"
        + "        return 0;\n"
        + "    }\n"
        + "}\n";

    /**
     * {@code int[][] a = new int[][]{{1,2}};}, a multi-dimensional array initializer (bad
     * construct 3).
     */
    private static final String BAD_INITIALIZER = "public class Bad {\n"
        + "    /*@ public normal_behavior\n"
        + "      @   ensures true;\n"
        + "      @*/\n"
        + "    public int m() {\n"
        + "        int[][] a = new int[][]{{1,2}};\n"
        + "        return 0;\n"
        + "    }\n"
        + "}\n";

    @Test
    void assignableStarStarIsReportedAsUnsupportedConstruct() throws IOException {
        ConstructNotSupportedException cause = loadAndExtract("star", BAD_STAR);

        assertEquals("bucketData[*][*]", cause.snippet());
        assertEquals(5, cause.line());
        assertEquals(22, cause.column());
        assertTrue(cause.file().endsWith("Bad.java"), "file: " + cause.file());
        assertEquals("bucketData[*][*]", cause.formattedMessage().split("construct '")[1]
                .split("' not supported:")[0]);
    }

    @Test
    void unsizedArrayCreationIsReportedAsUnsupportedConstruct() throws IOException {
        ConstructNotSupportedException cause = loadAndExtract("unsized", BAD_UNSIZED);

        assertEquals("new int[n][]", cause.snippet());
        assertEquals(6, cause.line());
        assertEquals(21, cause.column());
        assertTrue(cause.file().endsWith("Bad.java"), "file: " + cause.file());
    }

    @Test
    void multiDimensionalArrayInitializerIsReportedAsUnsupportedConstruct() throws IOException {
        ConstructNotSupportedException cause = loadAndExtract("initializer", BAD_INITIALIZER);

        assertEquals("new int[][]{{1,2}}", cause.snippet());
        assertEquals(6, cause.line());
        assertEquals(21, cause.column());
        assertTrue(cause.file().endsWith("Bad.java"), "file: " + cause.file());
    }

    @Test
    void formattedMessageFollowsTheDiagnosticFormat() throws IOException {
        ConstructNotSupportedException cause = loadAndExtract("unsized", BAD_UNSIZED);

        assertEquals(cause.file() + ":6:21: construct 'new int[n][]' not supported: "
            + cause.reason(), cause.formattedMessage());
    }

    @Test
    void exposesTheSourceLocation() {
        ConstructNotSupportedException cause =
            new ConstructNotSupportedException("/tmp/Bad.java", 5, 22, "x", "reason");

        var location = cause.getLocation();
        assertNotNull(location);
        assertEquals(5, location.position().line());
        assertEquals(22, location.position().column());
        assertNotNull(location.fileUri());
        assertTrue(location.fileUri().toString().endsWith("/tmp/Bad.java"));

        ConstructNotSupportedException unknown = new ConstructNotSupportedException(
            ConstructNotSupportedException.UNKNOWN_FILE, 0, 0, "x", "reason");
        assertNull(unknown.getLocation());
    }

    /**
     * Writes the given Java source plus a minimal load file into a fresh directory and loads it;
     * returns the {@link ConstructNotSupportedException} found in the cause chain.
     */
    private static ConstructNotSupportedException loadAndExtract(String name, String javaSource)
            throws IOException {
        Path dir = Files.createTempDirectory("construct-error-" + name);
        Files.writeString(dir.resolve("Bad.java"), javaSource);
        Path key = dir.resolve("index.key");
        Files.writeString(key,
            "\\profile \"Java Profile\";\n\n\\javaSource \".\";\n\n\\problem { true }\n");

        Throwable thrown;
        try {
            KeYEnvironment.load(key);
            fail("loading " + key + " was expected to fail with a structured construct error");
            throw new IllegalStateException("unreachable");
        } catch (Throwable t) {
            thrown = t;
        }

        // the crash modes the structured diagnostic replaces must be gone
        assertNull(findCause(thrown, NullPointerException.class), "still an NPE: " + thrown);
        assertNull(findCause(thrown, ClassCastException.class),
            "still a ClassCastException: " + thrown);

        ConstructNotSupportedException cause =
            findCause(thrown, ConstructNotSupportedException.class);
        assertNotNull(cause, "no ConstructNotSupportedException in the cause chain of: " + thrown);
        return cause;
    }

    /**
     * Returns the first throwable of the given type in the cause chain, or {@code null}.
     */
    private static <T extends Throwable> T findCause(Throwable throwable, Class<T> type) {
        Set<Throwable> seen = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
        for (Throwable c = throwable; c != null && seen.add(c); c = c.getCause()) {
            if (type.isInstance(c)) {
                return type.cast(c);
            }
        }
        return null;
    }
}
