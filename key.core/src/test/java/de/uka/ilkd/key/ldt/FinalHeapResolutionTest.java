/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ldt;

import java.util.TreeMap;

import de.uka.ilkd.key.settings.ProofSettings;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests for {@link FinalHeapResolution#isFinalEnabled(ProofSettings)}.
 *
 * <p>
 * In particular this pins down that an <em>absent</em> {@code finalFields} choice is resolved to
 * the declaration default {@code immutable} (the first option in the category, see
 * {@code optionsDeclarations.key} and {@code ChoiceFinder#visitChoice}). If it were resolved to
 * {@code onHeap} instead, the setting would disagree with the taclets that symbolic execution
 * actually applies, and reads of a final field would appear both as {@code final(o, f)} (from the
 * taclet base) and as {@code select(heap, o, f)} (from JML translation), which blocks otherwise
 * closable proofs.
 * </p>
 */
class FinalHeapResolutionTest {

    private static final String FINAL_FIELDS = "finalFields";

    private static ProofSettings settingsWith(String finalFieldsValue) {
        ProofSettings settings = new ProofSettings(ProofSettings.DEFAULT_SETTINGS);
        var choices = new TreeMap<>(settings.getChoiceSettings().getDefaultChoices());
        if (finalFieldsValue == null) {
            choices.remove(FINAL_FIELDS);
        } else {
            choices.put(FINAL_FIELDS, finalFieldsValue);
        }
        settings.getChoiceSettings().setDefaultChoices(choices);
        return settings;
    }

    @Test
    void absentChoiceDefaultsToImmutable() {
        assertTrue(FinalHeapResolution.isFinalEnabled(settingsWith(null)),
            "an absent finalFields choice must resolve to the declaration default 'immutable'");
    }

    @Test
    void explicitImmutableIsEnabled() {
        assertTrue(FinalHeapResolution.isFinalEnabled(settingsWith("finalFields:immutable")));
    }

    @Test
    void explicitOnHeapIsDisabled() {
        assertFalse(FinalHeapResolution.isFinalEnabled(settingsWith("finalFields:onHeap")));
    }
}
