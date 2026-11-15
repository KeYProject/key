/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.script;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.key_project.key.cli.Log;
import org.key_project.key.cli.Main;
import org.key_project.key.cli.Verbosity;
import org.key_project.key.cli.prove.Fixtures;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for the {@code script} subcommand and the §7.1 line protocol.
 */
class ScriptCommandTest {

    private static final String ONE_NAME = "C[C::one()].JML normal_behavior operation contract.0";

    private static final Pattern GOAL_LINE = Pattern.compile("^GOAL [0-9]+ ([1-9][0-9.]*)$");

    private static final Pattern COUNT_LINE = Pattern.compile("^OPEN-GOAL-COUNT ([0-9]+)$");

    @TempDir
    Path tempDir;

    @BeforeAll
    static void quietLogs() {
        Log.configureLogging(Verbosity.ERROR);
    }

    @Test
    @Timeout(900)
    void handScriptAppliesRulesAndOpenGoalsDrop() throws IOException {
        Path script = script(
            "# G3 acceptance script: split, inspect, close the provable branches, inspect again",
            "",
            "proceed",
            "apply impRight",
            "apply andLeft",
            "auto 40",
            "print-open-goals",
            "auto 500",
            "print-open-goals");

        Run run = run("script", sizeKey(), script.toString());

        assertThat(run.exit()).isEqualTo(1);
        // every non-comment command line reports OK, including the hand-applied rule
        assertThat(run.out()).contains("SCRIPT OK proceed");
        assertThat(run.out()).contains("SCRIPT OK apply impRight");
        assertThat(run.out()).contains("SCRIPT OK apply andLeft");
        assertThat(run.out()).contains("SCRIPT OK auto 40");
        assertThat(run.out()).contains("SCRIPT OK print-open-goals");
        assertThat(run.out()).contains("SCRIPT OK auto 500");
        assertThat(run.out()).doesNotContain("SCRIPT FAIL");
        // comments and empty lines are not echoed
        assertThat(run.out()).doesNotContain("G3 acceptance");

        // openGoals strictly drops between the first and the last print-open-goals
        List<Integer> counts = counts(run.out());
        assertThat(counts).hasSize(2);
        assertThat(counts.get(0)).isGreaterThanOrEqualTo(2);
        assertThat(counts.get(1)).isLessThan(counts.get(0));

        // every printed position path is usable by §7.1 `at`
        assertThat(goalPaths(run.out())).isNotEmpty()
                .allMatch(path -> path.matches("[1-9][0-9.]*"));

        // the last line is the final marker and reflects the true open-goal count
        assertThat(lastLine(run.out())).isEqualTo("SCRIPT FINAL open " + counts.get(1));
    }

    @Test
    @Timeout(600)
    void commentsAreIgnoredAndUnknownCommandFails() throws IOException {
        Path script = script("# only a comment", "", "frobnicate");

        Run run = run("script", sizeKey(), script.toString());

        assertThat(run.exit()).isEqualTo(1);
        assertThat(run.out()).doesNotContain("SCRIPT OK");
        assertThat(run.out()).contains("SCRIPT FAIL frobnicate Unknown command 'frobnicate'");
        assertThat(lastLine(run.out())).startsWith("SCRIPT FINAL open ");
    }

    @Test
    @Timeout(900)
    void assertClosedOnClosedProofPrintsFinalClosed() throws IOException {
        Path script = script("auto 1000", "assert-closed");

        Run run = run("script", Fixtures.indexKey().toString(), "--choose-contract", ONE_NAME,
            script.toString());

        assertThat(run.exit()).isZero();
        assertThat(run.out()).contains("SCRIPT OK auto 1000");
        assertThat(run.out()).contains("SCRIPT OK assert-closed");
        assertThat(lastLine(run.out())).isEqualTo("SCRIPT FINAL closed");
    }

    @Test
    @Timeout(600)
    void assertClosedOnOpenProofFails() throws IOException {
        Path script = script("assert-closed");

        Run run = run("script", sizeKey(), script.toString());

        assertThat(run.exit()).isEqualTo(1);
        assertThat(run.out()).contains("SCRIPT FAIL assert-closed");
        assertThat(lastLine(run.out())).isEqualTo("SCRIPT FINAL open 1");
    }

    @Test
    @Timeout(300)
    void timeoutFailsTheStrategyLineAndExitsTimedOut() throws IOException {
        Path script = script("auto 100000");

        Run run = run("script", "--timeout", "50", sizeKey(), script.toString());

        assertThat(run.exit()).isEqualTo(2);
        assertThat(run.out()).contains("SCRIPT FAIL auto 100000 timed out after");
        assertThat(run.out()).contains("SCRIPT FINAL open ");
    }

    @Test
    @Timeout(600)
    void missingScriptFileExitsWithInputError() {
        Run run = run("script", sizeKey(), tempDir.resolve("does-not-exist.script").toString());

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("KEY_ERROR");
        assertThat(run.out()).doesNotContain("SCRIPT");
    }

    @Test
    @Timeout(600)
    void scriptRequiresExactlyOneSelectedObligation() throws IOException {
        // index.key has two contracts; without a selector the script obligation is ambiguous
        Path script = script("# no commands");
        Run run = run("script", Fixtures.indexKey().toString(), script.toString());

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err())
                .contains("KEY_ERROR script requires exactly one selected obligation");
        assertThat(run.out()).doesNotContain("SCRIPT");
    }

    private Path script(String... lines) throws IOException {
        Path script = tempDir.resolve("proof.script");
        Files.write(script, List.of(lines));
        return script;
    }

    private static String sizeKey() {
        return Fixtures.resource("/fixtures/size/size.key").toString();
    }

    private static List<Integer> counts(String out) {
        List<Integer> counts = new ArrayList<>();
        for (String line : out.lines().toList()) {
            Matcher matcher = COUNT_LINE.matcher(line);
            if (matcher.matches()) {
                counts.add(Integer.parseInt(matcher.group(1)));
            }
        }
        return counts;
    }

    private static List<String> goalPaths(String out) {
        List<String> paths = new ArrayList<>();
        for (String line : out.lines().toList()) {
            Matcher matcher = GOAL_LINE.matcher(line);
            if (matcher.matches()) {
                paths.add(matcher.group(1));
            }
        }
        return paths;
    }

    private static String lastLine(String out) {
        List<String> lines = out.lines().toList();
        return lines.get(lines.size() - 1);
    }

    private record Run(int exit, String out, String err) {
    }

    private static Run run(String... args) {
        StringWriter out = new StringWriter();
        StringWriter err = new StringWriter();
        var cli = Main.createCommandLine();
        cli.setOut(new PrintWriter(out));
        cli.setErr(new PrintWriter(err));
        int exit = cli.execute(args);
        return new Run(exit, out.toString(), err.toString());
    }
}
