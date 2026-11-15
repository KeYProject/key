/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.settings;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatThrownBy;

/**
 * Tests for {@link HeadlessRunnerSettings}: the §5.1 precedence layering ({@code --strategy-option}
 * over {@code --settings-file} per key), the normalization of the documented {@code intRules}
 * shorthands to real KeY choice names, and the capture/restore of KeY's global default choices.
 */
class HeadlessRunnerSettingsTest {

    @AfterEach
    void restoreGlobalChoices() {
        // make each test independent of any leaked global choice state
        ProofSettings.DEFAULT_SETTINGS.getChoiceSettings()
                .setDefaultChoices(new HashMap<>());
    }

    @Test
    void strategyOptionWinsOverSettingsFilePerKey() {
        Map<String, String> file = Map.of(
            "intRules", "intRules:arithmeticSemanticsIgnoringOF",
            "bigint", "bigint:on");

        Map<String, String> merged = HeadlessRunnerSettings.layer(file,
            List.of("bigint=bigint:off"));

        assertThat(merged)
                .containsEntry("intRules", "intRules:arithmeticSemanticsIgnoringOF")
                .containsEntry("bigint", "bigint:off");
    }

    @Test
    void strategyOptionsLayerInCommandLineOrder() {
        Map<String, String> merged = HeadlessRunnerSettings.layer(Map.of(),
            List.of("intRules=intRules:unchecked", "intRules=intRules:javaSemantics"));

        assertThat(merged).containsEntry("intRules", "intRules:javaSemantics");
    }

    @Test
    void checkedIsNormalizedToTheRealChoiceName() {
        Map<String, String> merged = HeadlessRunnerSettings.layer(Map.of(),
            List.of("intRules=intRules:checked"));

        assertThat(merged).containsEntry("intRules", "intRules:arithmeticSemanticsCheckingOF");
    }

    @Test
    void uncheckedIsNormalizedToTheRealChoiceName() {
        Map<String, String> merged = HeadlessRunnerSettings.layer(Map.of(),
            List.of("intRules=intRules:unchecked"));

        assertThat(merged).containsEntry("intRules", "intRules:arithmeticSemanticsIgnoringOF");
    }

    @Test
    void settingsFileCheckedValueIsAlsoNormalized() {
        Map<String, String> file = Map.of("intRules", "intRules:checked");

        Map<String, String> merged = HeadlessRunnerSettings.layer(file, List.of());

        assertThat(merged).containsEntry("intRules", "intRules:arithmeticSemanticsCheckingOF");
    }

    @Test
    void valueKeYDoesNotDeclareIsRejected() {
        assertThatThrownBy(() -> HeadlessRunnerSettings.layer(Map.of(),
            List.of("programRules=programRules:JavaCard")))
                .isInstanceOf(CliSettingsException.class)
                .hasMessageContaining("not understood");
    }

    @Test
    void realDeclaredValuePassesThroughVerbatim() {
        Map<String, String> merged = HeadlessRunnerSettings.layer(Map.of(),
            List.of("programRules=programRules:None"));

        assertThat(merged).containsEntry("programRules", "programRules:None");
    }

    @Test
    void methodExpansionFullIsNormalizedToNoRestriction() {
        Map<String, String> merged = HeadlessRunnerSettings.layer(Map.of(),
            List.of("methodExpansion=methodExpansion:full"));

        assertThat(merged).containsEntry("methodExpansion", "methodExpansion:noRestriction");
    }

    @Test
    void validateRejectsAChoiceTheLoadedKeYDoesNotDeclare() {
        HeadlessRunnerSettings settings =
            HeadlessRunnerSettings.from(null, List.of("bigint=bigint:on"));

        assertThatThrownBy(() -> settings.validate(Map.of("bigint", Set.of("bigint:off"))))
                .isInstanceOf(CliSettingsException.class)
                .hasMessageContaining("not understood")
                .hasMessageContaining("bigint:off");
    }

    @Test
    void validateAcceptsADeclaredChoice() {
        HeadlessRunnerSettings settings =
            HeadlessRunnerSettings.from(null, List.of("bigint=bigint:on"));

        settings.validate(Map.of("bigint", Set.of("bigint:on", "bigint:off")));
    }

    @Test
    void strategyOptionWithoutEqualsSignIsRejected() {
        assertThatThrownBy(() -> HeadlessRunnerSettings.layer(Map.of(), List.of("intRules")))
                .isInstanceOf(CliSettingsException.class)
                .hasMessageContaining("not understood");
    }

    @Test
    void unknownStrategyOptionKeyIsRejected() {
        assertThatThrownBy(
            () -> HeadlessRunnerSettings.layer(Map.of(), List.of("nope=nope:on")))
                .isInstanceOf(CliSettingsException.class)
                .hasMessageContaining("not understood");
    }

    @Test
    void applySetsChoicesAndCloseRestoresThePreviousOnes() {
        ChoiceSettings cs = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
        // establish a known baseline so the test does not depend on ambient (possibly empty) state
        cs.setDefaultChoices(Map.of("bigint", "bigint:on"));
        Map<String, String> before = new HashMap<>(cs.getDefaultChoices());

        HeadlessRunnerSettings settings = HeadlessRunnerSettings.from(null,
            List.of("intRules=intRules:checked"));
        settings.apply();
        assertThat(cs.getDefaultChoices())
                .containsEntry("intRules", "intRules:arithmeticSemanticsCheckingOF");

        settings.close();
        assertThat(new HashMap<>(cs.getDefaultChoices())).isEqualTo(before);
    }

    @Test
    void closeWithoutApplyIsHarmless() {
        ChoiceSettings cs = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
        cs.setDefaultChoices(Map.of("bigint", "bigint:on"));
        Map<String, String> before = new HashMap<>(cs.getDefaultChoices());

        HeadlessRunnerSettings.from(null, List.of("intRules=intRules:checked")).close();

        assertThat(new HashMap<>(cs.getDefaultChoices())).isEqualTo(before);
    }
}
