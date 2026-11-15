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
 * Tests for the {@code prove} subcommand's multi-file result-record streaming (§2): each file's
 * {@code KEY_RESULT} records are printed as soon as that file's contracts have finished, so on a
 * run aborted by a later file the completed files' records are already on stdout, followed by the
 * failed file's error record as the last stdout line. For a completed run the records remain the
 * last N lines of stdout, in file order and, within a file, selection order.
 */
class ProveCommandMultiFileTest {

    @BeforeAll
    static void quietLogs() {
        Log.configureLogging(Verbosity.ERROR);
    }

    @Test
    @Timeout(300)
    void closedRecordOfCompletedFileSurvivesLaterLoadFailure() {
        Run run = run("prove", Fixtures.chooseKey().toString(), Fixtures.corruptKey().toString());

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("KEY_ERROR");
        // the closed record of the first file is printed as soon as that file finishes, so it
        // survives the abort caused by the unloadable second file, which is reported as an
        // error record
        List<String> resultLines = run.resultLines();
        assertThat(resultLines).hasSize(2);
        assertThat(resultLines.get(0)).contains("\"status\":\"closed\"");
        assertThat(resultLines.get(0)).contains("one()");
        assertThat(resultLines.get(1)).contains("\"status\":\"error\"");
        assertThat(resultLines.get(1)).contains("corrupt");
        assertThat(resultLines.get(1)).containsPattern("\"errorMessage\":\"[^\"]+\"");
        assertThat(resultLines.get(1)).doesNotContain("\"errorMessage\":null");
        // on abort the last stdout line remains a KEY_RESULT record
        List<String> stdoutLines = run.out().lines().toList();
        assertThat(stdoutLines).isNotEmpty();
        assertThat(stdoutLines.get(stdoutLines.size() - 1)).startsWith(ResultRecordWriter.PREFIX);
    }

    @Test
    @Timeout(300)
    void completedMultiFileRunPrintsRecordsInFileOrderAsLastLines() {
        Run run = run("prove", Fixtures.indexKey().toString(), Fixtures.chooseKey().toString());

        assertThat(run.exit()).isEqualTo(1);
        assertThat(run.err()).doesNotContain("KEY_ERROR");
        // file order: index.key proves one() (closed) and two() (open) in index order,
        // then choose.key proves its directed one() (closed)
        List<String> resultLines = run.resultLines();
        assertThat(resultLines).hasSize(3);
        assertThat(resultLines.get(0)).contains("\"status\":\"closed\"");
        assertThat(resultLines.get(0)).contains("one()");
        assertThat(resultLines.get(1)).contains("\"status\":\"open\"");
        assertThat(resultLines.get(1)).contains("two()");
        assertThat(resultLines.get(2)).contains("\"status\":\"closed\"");
        assertThat(resultLines.get(2)).contains("one()");
        // a completed run still prints the records as the last lines of stdout
        List<String> stdoutLines = run.out().lines().toList();
        assertThat(stdoutLines).hasSize(3);
        assertThat(stdoutLines.get(2)).startsWith(ResultRecordWriter.PREFIX);
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
        cli.setOut(new ProtocolWriter(out));
        cli.setErr(new ProtocolWriter(err));
        int exit = cli.execute(args);
        return new Run(exit, out.toString(), err.toString());
    }
}
