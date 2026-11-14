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
 * Tests for the {@code --choose-contract} selectors of the {@code prove} subcommand (§4.2, §4.4
 * of the headless interface spec).
 */
class ProveCommandSelectionTest {

    private static final String ONE_NAME = "C[C::one()].JML normal_behavior operation contract.0";
    private static final String TWO_NAME = "C[C::two()].JML normal_behavior operation contract.0";

    @BeforeAll
    static void quietLogs() {
        Log.configureLogging(Verbosity.ERROR);
    }

    @Test
    @Timeout(300)
    void choosesContractByExactName() {
        Run run = run("prove", Fixtures.indexKey().toString(), "--choose-contract", ONE_NAME);

        assertThat(run.exit()).isZero();
        assertThat(run.resultLines()).hasSize(1);
        assertThat(run.out()).contains("\"contract\":\"" + ONE_NAME + "\"");
        assertThat(run.out()).contains("\"status\":\"closed\"");
        assertThat(run.out()).contains("\"openGoals\":0");
    }

    @Test
    @Timeout(300)
    void choosesOpenContractByExactName() {
        Run run = run("prove", Fixtures.indexKey().toString(), "--choose-contract", TWO_NAME);

        assertThat(run.exit()).isEqualTo(1);
        assertThat(run.resultLines()).hasSize(1);
        assertThat(run.out()).contains("\"contract\":\"" + TWO_NAME + "\"");
        assertThat(run.out()).contains("\"status\":\"open\"");
        assertThat(run.out()).containsPattern("\"openGoals\":[1-9][0-9]*");
    }

    @Test
    @Timeout(300)
    void sameNameTwiceProducesTwoRecords() {
        Run run = run("prove", Fixtures.indexKey().toString(), "--choose-contract", ONE_NAME,
            "--choose-contract", ONE_NAME);

        assertThat(run.exit()).isZero();
        assertThat(run.resultLines()).hasSize(2);
        assertThat(run.out()).contains("\"status\":\"closed\"");
        assertThat(run.out()).doesNotContain("\"status\":\"open\"");
    }

    @Test
    @Timeout(300)
    void choosesContractByBareIndexLikeTheListingRow() {
        // D2-style: row 0 of the listing is the one() contract; the bare index selects it
        Run run = run("prove", Fixtures.indexKey().toString(), "--choose-contract", "0");

        assertThat(run.exit()).isZero();
        assertThat(run.resultLines()).hasSize(1);
        assertThat(run.out()).contains("\"contract\":\"" + ONE_NAME + "\"");
        assertThat(run.out()).contains("\"status\":\"closed\"");
    }

    @Test
    @Timeout(300)
    void choosesOverloadByNameAndIndex() {
        Run run =
            run("prove", Fixtures.indexKey().toString(), "--choose-contract", TWO_NAME + ".#1");

        assertThat(run.exit()).isEqualTo(1);
        assertThat(run.resultLines()).hasSize(1);
        assertThat(run.out()).contains("\"contract\":\"" + TWO_NAME + "\"");
        assertThat(run.out()).contains("\"status\":\"open\"");
    }

    @Test
    @Timeout(300)
    void nameAndIndexMismatchIsNotFound() {
        Run run =
            run("prove", Fixtures.indexKey().toString(), "--choose-contract", ONE_NAME + ".#1");

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("KEY_ERROR contract '" + ONE_NAME + ".#1' not found");
    }

    @Test
    @Timeout(300)
    void unknownSelectorPrintsErrorAndFullListing() {
        Run run = run("prove", Fixtures.indexKey().toString(), "--choose-contract", "NoSuch");

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("KEY_ERROR contract 'NoSuch' not found");
        assertThat(run.resultLines()).isEmpty();
        assertThat(run.out().lines().toList()).containsExactly(
            "0\tC::one\t" + ONE_NAME, "1\tC::two\t" + TWO_NAME);
    }

    @Test
    @Timeout(300)
    void selectionOrderFollowsTheCommandLine() {
        Run run = run("prove", Fixtures.indexKey().toString(), "--choose-contract", TWO_NAME,
            "--choose-contract", ONE_NAME);

        assertThat(run.exit()).isEqualTo(1);
        assertThat(run.resultLines()).hasSize(2);
        // the KEY_RESULT lines follow the selection (command-line) order
        assertThat(run.out()).contains("\"contract\":\"" + TWO_NAME + "\"")
                .contains("\"contract\":\"" + ONE_NAME + "\"");
        int twoIdx = run.out().indexOf("\"contract\":\"" + TWO_NAME + "\"");
        int oneIdx = run.out().indexOf("\"contract\":\"" + ONE_NAME + "\"");
        assertThat(twoIdx).isLessThan(oneIdx);
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
