/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.List;

import org.key_project.key.cli.Log;
import org.key_project.key.cli.Main;
import org.key_project.key.cli.ResultRecordWriter;
import org.key_project.key.cli.Verbosity;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for the CLI-level error classification (§1): input errors (unknown option, missing file,
 * corrupt load file, unknown contract) exit {@code 3} with a {@code KEY_ERROR} line on stderr,
 * while an unloadable load file additionally emits an error record whose {@code errorMessage} is
 * non-{@code null}.
 */
class ProveCommandErrorTest {

    @BeforeAll
    static void quietLogs() {
        Log.configureLogging(Verbosity.ERROR);
    }

    @Test
    @Timeout(120)
    void corruptKeyFileIsAnInputErrorWithKeyErrorAndErrorRecord() {
        Run run = run("prove", Fixtures.corruptKey().toString());

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("KEY_ERROR");
        // the failed file is still reported as an error record with a non-null errorMessage
        assertThat(run.resultLines()).hasSize(1);
        String record = run.resultLines().get(0);
        assertThat(record).contains("\"status\":\"error\"");
        assertThat(record).contains("corrupt");
        assertThat(record).containsPattern("\"errorMessage\":\"[^\"]+\"");
        assertThat(record).doesNotContain("\"errorMessage\":null");
    }

    @Test
    @Timeout(120)
    void unknownOptionIsAnInputError() {
        Run run = run("prove", Fixtures.indexKey().toString(), "--definitely-not-an-option");

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("KEY_ERROR");
        assertThat(run.resultLines()).isEmpty();
    }

    @Test
    @Timeout(120)
    void missingValueForTimeoutOptionIsAnInputError() {
        Run run = run("prove", Fixtures.indexKey().toString(), "--timeout");

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("KEY_ERROR");
    }

    @Test
    @Timeout(120)
    void nonNumericTimeoutIsAnInputError() {
        Run run = run("prove", Fixtures.indexKey().toString(), "--timeout", "abc");

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("KEY_ERROR");
        assertThat(run.resultLines()).isEmpty();
    }

    @Test
    @Timeout(300)
    void unknownContractIsAnInputErrorWithFullListing() {
        Run run =
            run("prove", Fixtures.indexKey().toString(), "--choose-contract", "NoSuchContract");

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("KEY_ERROR contract 'NoSuchContract' not found");
        assertThat(run.resultLines()).isEmpty();
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
