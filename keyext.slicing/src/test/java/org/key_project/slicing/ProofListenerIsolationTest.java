/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;

import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.settings.GeneralSettings;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Verifies that {@code Proof} isolates its listeners: a {@link RuleAppListener} such as the slicing
 * {@link DependencyTracker} is notified from within {@code Goal.apply} (via
 * {@code Proof.fireRuleApplied}), so if it throws, the exception must not abort the proof search
 * and
 * leave the proof inconsistent. Instead the proof logs the failure, unregisters the offending
 * listener, and carries on. This is the general safety net behind the {@link DependencyTracker}
 * fast-click crash (a tracking failure used to escape into the proof search).
 */
public class ProofListenerIsolationTest {
    private static final Path testCaseDirectory = FindResources.getTestCasesDirectory();

    @Test
    void aThrowingRuleAppListenerDoesNotBreakTheProofAndIsUnregistered() throws Exception {
        GeneralSettings.noPruningClosed = false;
        var file = testCaseDirectory.resolve(
            "issues/3834/SumAndMax(SumAndMax__sumAndMax((I)).JML normal_behavior operation contract.0.proof");
        var env = KeYEnvironment.load(file);
        try {
            var proof = env.getLoadedProof();

            // A rogue listener that always throws when a rule is applied.
            int[] callCount = { 0 };
            RuleAppListener rogue = e -> {
                callCount[0]++;
                throw new IllegalStateException("boom from a rogue rule-app listener");
            };
            proof.addRuleAppListener(rogue);

            // Re-run auto mode so rules are applied and the listener fires.
            proof.pruneProof(proof.findAny(x -> x.serialNr() == 13));
            env.getProofControl().startAutoMode(proof, proof.openEnabledGoals());
            env.getProofControl().waitWhileAutoMode();

            // The rogue listener did not stop the proof search ...
            assertTrue(proof.closed(), "a throwing listener must not stop the proof from closing");
            // ... and it was unregistered after its first failure, so it fires at most once.
            assertEquals(1, callCount[0],
                "a throwing rule-app listener should be unregistered after it throws");
        } finally {
            env.dispose();
            GeneralSettings.noPruningClosed = true;
        }
    }
}
