/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import de.uka.ilkd.key.prover.impl.ParallelProver;
import de.uka.ilkd.key.rule.merge.MergeRule;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Verifies that {@link MergeRule} disables itself while a multi-worker parallel run is active.
 *
 * <p>
 * MergeRule links several goals into one and would need to lock multiple goals at once, which is
 * not
 * yet safe under goal-level concurrency, so it is switched off for the duration of a multi-worker
 * run (single-threaded proving keeps it). This test pins the gating mechanism
 * ({@link ParallelProver#isMultiThreadedRunActive()} /
 * {@link ParallelProver#enterMultiThreadedRun()})
 * and that {@code MergeRule.isApplicable} consults it. A full end-to-end test (a mergeable proof
 * under several workers) is deferred until the lock-narrowing step.
 *
 * @author Claude (KeY multithreading effort)
 */
public class MergeRuleMultiThreadGuardTest {

    @Test
    void runScopeTogglesTheActiveFlagAndBalances() {
        assertFalse(ParallelProver.isMultiThreadedRunActive(), "must be inactive by default");
        try (var outer = ParallelProver.enterMultiThreadedRun()) {
            assertTrue(ParallelProver.isMultiThreadedRunActive());
            try (var inner = ParallelProver.enterMultiThreadedRun()) {
                assertTrue(ParallelProver.isMultiThreadedRunActive(), "nested scope still active");
            }
            assertTrue(ParallelProver.isMultiThreadedRunActive(),
                "outer scope keeps it active after inner closes");
        }
        assertFalse(ParallelProver.isMultiThreadedRunActive(), "must be inactive after all scopes");
    }

    @Test
    void mergeRuleIsDisabledWhileMultiThreadedRunActive() {
        // The guard short-circuits before touching its arguments, so null is safe here.
        try (var scope = ParallelProver.enterMultiThreadedRun()) {
            assertFalse(MergeRule.INSTANCE.isApplicable(null, null),
                "MergeRule must be inapplicable while a multi-worker run is active");
        }
        assertFalse(ParallelProver.isMultiThreadedRunActive());
    }
}
