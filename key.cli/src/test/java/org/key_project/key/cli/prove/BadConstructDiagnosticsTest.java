/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.io.StringWriter;
import java.util.List;

import org.key_project.key.cli.Log;
import org.key_project.key.cli.Main;
import org.key_project.key.cli.ProtocolWriter;
import org.key_project.key.cli.ResultRecordWriter;
import org.key_project.key.cli.Verbosity;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for the §8 construct diagnostics: the three constructs listed in the spec
 * ({@code assignable bucketData[*][*];}, {@code new int[n][]}, {@code new int[][]{{1,2}}}) must
 * each fail the run with exit {@code 3} and exactly one structured {@code KEY_ERROR} line on
 * stderr, {@code KEY_ERROR <file>:<line>:<col>: construct '<snippet>' not supported:
 * <reason>}, with the exact snippet and the 1-based line/column of the construct in the source —
 * never an NPE or a stack trace.
 */
class BadConstructDiagnosticsTest {

    @BeforeAll
    static void quietLogs() {
        Log.configureLogging(Verbosity.ERROR);
    }

    @Test
    @Timeout(120)
    void starStarAssignableExits3WithStructuredKeyError() {
        Run run = run("prove", Fixtures.bucketStarKey().toString());
        assertConstructError(run, "bucket-star", "5:22", "bucketData[*][*]");
    }

    @Test
    @Timeout(120)
    void unsizedArrayCreationExits3WithStructuredKeyError() {
        Run run = run("prove", Fixtures.unsizedNewKey().toString());
        assertConstructError(run, "unsized-new", "6:21", "new int[n][]");
    }

    @Test
    @Timeout(120)
    void multiDimensionalArrayInitializerExits3WithStructuredKeyError() {
        Run run = run("prove", Fixtures.initNewKey().toString());
        assertConstructError(run, "init-new", "6:21", "new int[][]{{1,2}}");
    }

    @Test
    @Timeout(120)
    void badConstructsAreReportedTheSameWayByList() {
        Run run = run("list", Fixtures.bucketStarKey().toString());

        assertThat(run.exit()).isEqualTo(3);
        List<String> keyErrorLines = run.errLines().stream()
                .filter(line -> line.startsWith("KEY_ERROR")).toList();
        assertThat(keyErrorLines).hasSize(1);
        assertThat(keyErrorLines.get(0))
                .matches(
                    "KEY_ERROR .+[\\\\/]acceptance[\\\\/]bucket-star[\\\\/]Bad\\.java:5:22: construct "
                        + "'bucketData\\[\\*\\]\\[\\*\\]' not supported: .+");
        assertThat(run.err()).doesNotContain("NullPointerException", "ClassCastException",
            "at de.uka");
        assertThat(run.resultLines()).isEmpty();
    }

    /**
     * The combined suite (acceptance H1): one run per bad construct produces exactly one
     * {@code KEY_ERROR} line each, i.e. the total count equals the number of bad constructs.
     */
    @Test
    @Timeout(300)
    void combinedSuiteKeyErrorCountEqualsNumberOfBadConstructs() {
        List<Run> runs =
            Fixtures.badConstructKeys().stream().map(key -> run("prove", key.toString()))
                    .toList();

        long keyErrorLines = 0;
        for (Run run : runs) {
            assertThat(run.exit()).isEqualTo(3);
            keyErrorLines +=
                run.errLines().stream().filter(line -> line.startsWith("KEY_ERROR")).count();
        }
        // H1: the KEY_ERROR line count equals the number of bad constructs
        assertThat(keyErrorLines)
                .as("KEY_ERROR lines across all runs: %s", runs).isEqualTo(runs.size());
    }

    private static void assertConstructError(Run run, String fixtureDir, String lineCol,
            String snippet) {
        assertThat(run.exit()).isEqualTo(3);
        List<String> keyErrorLines = run.errLines().stream()
                .filter(line -> line.startsWith("KEY_ERROR")).toList();
        assertThat(keyErrorLines).as("stderr: %s", run.err()).hasSize(1);
        assertThat(keyErrorLines.get(0))
                .matches("KEY_ERROR .+[\\\\/]acceptance[\\\\/]" + fixtureDir + "[\\\\/]Bad\\.java:"
                    + lineCol + ": construct '" + snippetToRegex(snippet) + "' not supported: .+");
        // no crash: never an NPE/CCE or a stack trace on stderr
        assertThat(run.err()).doesNotContain("NullPointerException", "ClassCastException",
            "at de.uka");
        // the failed file is reported as one error record whose errorMessage carries the
        // structured diagnostic
        assertThat(run.resultLines()).hasSize(1);
        assertThat(run.resultLines().get(0)).contains("\"status\":\"error\"")
                .containsPattern("construct '" + snippetToRegex(snippet) + "' not supported:");
    }

    private static String snippetToRegex(String snippet) {
        return java.util.regex.Pattern.quote(snippet);
    }

    private record Run(int exit, String out, String err) {
        List<String> resultLines() {
            return out.lines().filter(line -> line.startsWith(ResultRecordWriter.PREFIX)).toList();
        }

        List<String> errLines() {
            return err.lines().toList();
        }
    }

    private static Run run(String... args) {
        StringWriter out = new StringWriter();
        StringWriter err = new StringWriter();
        var cli = Main.createCommandLine();
        cli.setOut(new ProtocolWriter(out));
        cli.setErr(new ProtocolWriter(err));
        int exit = cli.execute(args);
        return new Run(exit, out.toString(), err.toString());
    }
}
