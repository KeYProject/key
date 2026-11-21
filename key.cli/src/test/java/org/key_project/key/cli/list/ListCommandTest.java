/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.list;

import java.io.StringWriter;

import org.key_project.key.cli.Log;
import org.key_project.key.cli.Main;
import org.key_project.key.cli.ProtocolWriter;
import org.key_project.key.cli.Verbosity;
import org.key_project.key.cli.prove.Fixtures;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for the {@code list} subcommand (§4.3 of the headless interface spec).
 */
class ListCommandTest {

    private static final String ONE_NAME = "C[C::one()].JML normal_behavior operation contract.0";
    private static final String TWO_NAME = "C[C::two()].JML normal_behavior operation contract.0";

    @BeforeAll
    static void quietLogs() {
        Log.configureLogging(Verbosity.ERROR);
    }

    @Test
    @Timeout(300)
    void printsTabSeparatedRowsByteExact() {
        Run run = run("list", Fixtures.indexKey().toString());

        assertThat(run.exit()).isZero();
        // byte-exact §4.3 rows: <IDX>\t<target>\t<NAME>, one per contract, no KEY_RESULT
        assertThat(run.out())
                .isEqualTo("0\tC::one\t" + ONE_NAME + "\n1\tC::two\t" + TWO_NAME + "\n");
        assertThat(run.out()).doesNotContain("KEY_RESULT");
    }

    @Test
    @Timeout(600)
    void isDeterministicAcrossRuns() {
        Run first = run("list", Fixtures.indexKey().toString());
        Run second = run("list", Fixtures.indexKey().toString());

        assertThat(first.exit()).isZero();
        assertThat(second.exit()).isZero();
        assertThat(first.out()).isEqualTo(second.out());
    }

    @Test
    @Timeout(120)
    void missingFileExitsWithInputError() {
        Run run = run("list", "/nonexistent/does-not-exist.key");

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("KEY_ERROR");
        assertThat(run.out()).doesNotContain("KEY_RESULT");
    }

    private record Run(int exit, String out, String err) {
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
