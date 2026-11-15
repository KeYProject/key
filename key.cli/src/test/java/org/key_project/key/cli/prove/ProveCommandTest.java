/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.io.StringWriter;

import org.key_project.key.cli.Main;
import org.key_project.key.cli.ProtocolWriter;
import org.key_project.key.cli.ResultRecordWriter;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for the {@code prove} subcommand and its exit-code mapping.
 */
class ProveCommandTest {

    @BeforeAll
    static void quietLogs() {
        org.key_project.key.cli.Log.configureLogging(org.key_project.key.cli.Verbosity.ERROR);
    }

    @Test
    @Timeout(300)
    void provesFixtureAndPrintsOneResultLinePerContract() throws Exception {
        StringWriter out = new StringWriter();
        StringWriter err = new StringWriter();
        var cli = Main.createCommandLine();
        cli.setOut(new ProtocolWriter(out));
        cli.setErr(new ProtocolWriter(err));

        // the fixture contains one closed and one open contract
        int exit = cli.execute("prove", Fixtures.indexKey().toString());

        assertThat(exit).isEqualTo(1);
        String[] lines = out.toString().split("\n");
        assertThat(lines).hasSize(2);
        assertThat(lines[0]).startsWith(ResultRecordWriter.PREFIX);
        assertThat(lines[0]).contains("\"status\":\"closed\"");
        assertThat(lines[1]).startsWith(ResultRecordWriter.PREFIX);
        assertThat(lines[1]).contains("\"status\":\"open\"");
        // the KEY_RESULT lines are the last lines of stdout
        assertThat(out.toString().trim()).isEqualTo(lines[0] + "\n" + lines[1]);
        assertThat(err.toString()).doesNotContain("KEY_ERROR");
    }

    @Test
    @Timeout(120)
    void missingFileExitsWithInputErrorAndKeyError() {
        StringWriter out = new StringWriter();
        StringWriter err = new StringWriter();
        var cli = Main.createCommandLine();
        cli.setOut(new ProtocolWriter(out));
        cli.setErr(new ProtocolWriter(err));

        int exit = cli.execute("prove", "/nonexistent/does-not-exist.key");

        assertThat(exit).isEqualTo(3);
        assertThat(err.toString()).contains("KEY_ERROR");
        assertThat(out.toString()).doesNotContain("KEY_RESULT");
    }

    @Test
    @Timeout(120)
    void unknownOptionExitsWithInputError() {
        StringWriter out = new StringWriter();
        StringWriter err = new StringWriter();
        var cli = Main.createCommandLine();
        cli.setOut(new ProtocolWriter(out));
        cli.setErr(new ProtocolWriter(err));

        int exit = cli.execute("prove", "--definitely-not-an-option");

        assertThat(exit).isEqualTo(3);
        assertThat(err.toString()).contains("KEY_ERROR");
    }

    @Test
    @Timeout(120)
    void missingPositionalsExitsWithInputError() {
        StringWriter out = new StringWriter();
        StringWriter err = new StringWriter();
        var cli = Main.createCommandLine();
        cli.setOut(new ProtocolWriter(out));
        cli.setErr(new ProtocolWriter(err));

        int exit = cli.execute("prove");

        assertThat(exit).isEqualTo(3);
        assertThat(err.toString()).contains("KEY_ERROR");
    }

    @Test
    @Timeout(120)
    void noSubcommandExitsWithInputError() {
        StringWriter out = new StringWriter();
        StringWriter err = new StringWriter();
        var cli = Main.createCommandLine();
        cli.setOut(new ProtocolWriter(out));
        cli.setErr(new ProtocolWriter(err));

        int exit = cli.execute();

        assertThat(exit).isEqualTo(3);
        assertThat(err.toString()).contains("KEY_ERROR");
    }
}
