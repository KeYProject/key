/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.List;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;

import org.key_project.key.cli.ContractResult;
import org.key_project.key.cli.Log;
import org.key_project.key.cli.Main;
import org.key_project.key.cli.ResultRecordWriter;
import org.key_project.key.cli.ResultStatus;
import org.key_project.key.cli.Verbosity;
import org.key_project.key.cli.settings.HeadlessRunnerSettings;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * End-to-end tests for the §5 settings sources of the {@code prove} command: rejection of an
 * unknown settings key (matrix row 6) and of an undocumented strategy value, the visibility of a
 * {@code --settings-file} choice in the run's proof header (E1), and the effect of the
 * {@code intRules} checked/unchecked strategy options on an overflow-sensitive contract (E3).
 */
class ProveCommandSettingsTest {

    @BeforeAll
    static void quietLogs() {
        Log.configureLogging(Verbosity.ERROR);
    }

    @Test
    @Timeout(120)
    void unknownSettingsKeyIsAnInputError() {
        Run run = run("prove", Fixtures.indexKey().toString(),
            "--settings-file", Fixtures.unknownKeySettings().toString());

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("KEY_ERROR settings:");
        assertThat(run.resultLines()).isEmpty();
    }

    @Test
    @Timeout(120)
    void typoStrategyOptionValueIsAnInputError() {
        Run run = run("prove", Fixtures.indexKey().toString(),
            "--strategy-option", "intRules=intRules:javaSemantic");

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("KEY_ERROR settings:");
        assertThat(run.resultLines()).isEmpty();
    }

    @Test
    @Timeout(300)
    void legacyValueKeYDoesNotDeclareIsAnInputError() {
        Run run = run("prove", Fixtures.indexKey().toString(),
            "--strategy-option", "javaLoopTreatment=javaLoopTreatment:default");

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("KEY_ERROR settings:");
        assertThat(run.err()).contains("javaLoopTreatment:default");
        assertThat(run.resultLines()).isEmpty();
    }

    @Test
    @Timeout(300)
    void methodExpansionFullShorthandIsAccepted() {
        Run run = run("prove", Fixtures.indexKey().toString(), "--choose-contract", "0",
            "--strategy-option", "methodExpansion=methodExpansion:full");

        assertThat(run.exit()).isZero();
        assertThat(run.resultLines()).hasSize(1);
    }

    @Test
    @Timeout(120)
    void strategyOptionWithoutEqualsIsAnInputError() {
        Run run = run("prove", Fixtures.indexKey().toString(), "--strategy-option", "intRules");

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("KEY_ERROR settings:");
        assertThat(run.resultLines()).isEmpty();
    }

    @Test
    @Timeout(120)
    void missingSettingsFileIsAnInputError() {
        Run run = run("prove", Fixtures.indexKey().toString(),
            "--settings-file", "/nonexistent/settings.json");

        assertThat(run.exit()).isEqualTo(3);
        assertThat(run.err()).contains("KEY_ERROR");
        assertThat(run.resultLines()).isEmpty();
    }

    /**
     * E1: a {@code --settings-file} that sets {@code intRules:javaSemantics} makes that choice
     * visible in the run's proof settings, i.e. it changes the strategy manifest of the proof.
     *
     * @throws Exception if the fixture cannot be loaded
     */
    @Test
    @Timeout(120)
    void settingsFileMakesIntRulesVisibleInTheProofHeader() throws Exception {
        HeadlessRunnerSettings settings = HeadlessRunnerSettings.from(Fixtures.fullSettings(),
            List.of());
        settings.apply();
        try {
            KeYEnvironment<DefaultUserInterfaceControl> environment =
                KeYEnvironment.load(Fixtures.indexKey());
            try {
                String intRules = environment.getLoadedProof().getSettings().getChoiceSettings()
                        .getDefaultChoices().get("intRules");
                assertThat(intRules == null ? "<absent>" : intRules)
                        .isEqualTo("intRules:javaSemantics");
            } finally {
                environment.dispose();
            }
        } finally {
            settings.close();
        }
    }

    /**
     * E3: the {@code intRules=checked} and {@code intRules=unchecked} strategy options produce
     * different proof outcomes on an overflow-sensitive contract. Under the unchecked (ignoring
     * overflow) semantics the contract closes; under the checked semantics the additional overflow
     * obligation stays open.
     *
     * @throws Exception if the fixture cannot be loaded
     */
    @Test
    @Timeout(300)
    void intRulesCheckedAndUncheckedDifferOnAnOverflowContract() throws Exception {
        ContractResult unchecked = proveOverflow("intRules=intRules:unchecked");
        ContractResult checked = proveOverflow("intRules=intRules:checked");

        // the pair must differ (the E3 requirement); concretely unchecked closes, checked stays
        // open
        assertThat(outcome(unchecked)).isNotEqualTo(outcome(checked));
        assertThat(unchecked.status()).isEqualTo(ResultStatus.CLOSED);
        assertThat(checked.status()).isEqualTo(ResultStatus.OPEN);
        assertThat(checked.openGoals()).isGreaterThan(0);
    }

    private static String outcome(ContractResult result) {
        return result.status() + "/" + result.openGoals();
    }

    private static ContractResult proveOverflow(String strategyOption) throws Exception {
        HeadlessRunnerSettings settings = HeadlessRunnerSettings.from(null,
            List.of(strategyOption));
        List<ContractResult> results =
            new HeadlessProver(0, settings).proveAll(Fixtures.overflowKey());
        assertThat(results).hasSize(1);
        return results.get(0);
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
