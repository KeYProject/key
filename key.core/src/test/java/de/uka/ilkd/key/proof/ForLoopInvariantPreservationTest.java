/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof;

import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.settings.ProofSettings;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Pins that a JML loop invariant attached to a {@code for} loop survives the translation into the
 * proof and the subsequent {@code for}-to-{@code while} transformation. The example used here
 * failed to close because the invariants were dropped, leaving the loop goals open.
 */
class ForLoopInvariantPreservationTest {

    private static String settingsSnapshot;

    @BeforeAll
    static void snapshotSettings() {
        settingsSnapshot = ProofSettings.DEFAULT_SETTINGS.settingsToString();
    }

    @AfterAll
    static void restoreSettings() {
        ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(settingsSnapshot);
    }

    @Test
    void automaticProofClosesAddAndMultiply() throws Exception {
        Path keyFile = FindResources.getExampleDirectory()
                .resolve("heap/WeideEtAl_01_AddAndMultiply/AddAndMultiply_add.key");

        KeYEnvironment<?> env = KeYEnvironment.load(keyFile);
        try {
            Proof proof = env.getLoadedProof();
            env.getProofControl().startAndWaitForAutoMode(proof);
            assertTrue(proof.closed(),
                "auto mode left " + proof.openGoals().size()
                    + " goal(s) open; the for-loop invariants were not applied");
        } finally {
            env.dispose();
        }
    }
}
