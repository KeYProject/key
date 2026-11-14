/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.key_project.key.cli.Log;
import org.key_project.key.cli.Main;
import org.key_project.key.cli.ResultRecordWriter;
import org.key_project.key.cli.Verbosity;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for the {@code --timeout} option of the {@code prove} subcommand (§1, acceptance A1/A3
 * of the headless interface spec): a proof search abandoned by the timeout is reported as
 * {@code "status":"timed_out"} with exit code {@code 2}, while a strategy that exhausts its
 * rules before the timeout elapses stays {@code "status":"open"} with exit code {@code 1}.
 */
class ProveCommandTimeoutTest {

    private static final String ONE_NAME = "C[C::one()].JML normal_behavior operation contract.0";
    private static final String TWO_NAME = "C[C::two()].JML normal_behavior operation contract.0";

    @BeforeAll
    static void quietLogs() {
        Log.configureLogging(Verbosity.ERROR);
    }

    /** A3: a 1 ms timeout on the known-open contract yields {@code timed_out} and exit 2. */
    @Test
    @Timeout(120)
    void oneMillisecondTimeoutOnOpenContractIsTimedOut() {
        Run run = run("prove", Fixtures.indexKey().toString(), "--choose-contract", TWO_NAME,
            "--timeout", "1");

        assertThat(run.exit()).isEqualTo(2);
        assertThat(run.resultLines()).hasSize(1);
        assertThat(run.out()).contains("\"status\":\"timed_out\"");
        assertThat(run.out()).contains("\"contract\":\"" + TWO_NAME + "\"");
        // the search was abandoned early, not after exhausting the strategy
        assertThat(elapsedMsOf(run.resultLines().get(0))).isLessThan(10_000L);
        assertThat(errIsEmpty(run)).isTrue();
    }

    /** A1: a generous timeout on the closed contract still closes with exit 0. */
    @Test
    @Timeout(300)
    void largeTimeoutOnClosedContractStaysClosed() {
        Run run = run("prove", Fixtures.indexKey().toString(), "--choose-contract", ONE_NAME,
            "--timeout", "30000");

        assertThat(run.exit()).isZero();
        assertThat(run.resultLines()).hasSize(1);
        assertThat(run.out()).contains("\"status\":\"closed\"");
        assertThat(run.out()).contains("\"openGoals\":0");
    }

    /**
     * Regression: the known-open contract with a timeout that does not elapse must stay
     * {@code open} (exit 1), not {@code timed_out} (exit 2).
     */
    @Test
    @Timeout(300)
    void largeTimeoutOnOpenContractStaysOpen() {
        Run run = run("prove", Fixtures.indexKey().toString(), "--choose-contract", TWO_NAME,
            "--timeout", "300000");

        assertThat(run.exit()).isEqualTo(1);
        assertThat(run.resultLines()).hasSize(1);
        assertThat(run.out()).contains("\"status\":\"open\"");
        assertThat(run.out()).doesNotContain("\"status\":\"timed_out\"");
        assertThat(run.out()).containsPattern("\"openGoals\":[1-9][0-9]*");
    }

    @Test
    @Timeout(120)
    void negativeTimeoutIsAnInputError() {
        Run run = run("prove", Fixtures.indexKey().toString(), "--timeout", "-1");

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("KEY_ERROR");
        assertThat(run.resultLines()).isEmpty();
    }

    private static long elapsedMsOf(String resultLine) {
        Matcher m = Pattern.compile("\"elapsedMs\":(\\d+)").matcher(resultLine);
        assertThat(m.find()).as("elapsedMs in <%s>", resultLine).isTrue();
        String value = m.group(1);
        if (value == null) {
            throw new AssertionError("elapsedMs capture group is null in " + resultLine);
        }
        return Long.parseLong(value);
    }

    private static boolean errIsEmpty(Run run) {
        return !run.err().contains("KEY_ERROR");
    }

    private record Run(int exit, String out, String err) {
        List<String> resultLines() {
            return out.lines().filter(line -> line.startsWith(ResultRecordWriter.PREFIX)).toList();
        }
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
