/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ParallelProver;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Verifies that {@link MergeRule} disables itself while a multi-worker parallel run is active on
 * its proof -- and only on its proof.
 *
 * <p>
 * MergeRule links several goals into one and would need to lock multiple goals at once, which is
 * not yet safe under goal-level concurrency, so it is switched off for the duration of a
 * multi-worker run (single-threaded proving keeps it). The run marker is scoped per proof
 * ({@link ParallelProver#isMultiThreadedRunActive(org.key_project.prover.proof.ProofObject)}):
 * several proofs may be processed in parallel in one JVM, and a proof that is being proved
 * single-core -- including a side proof spawned by a worker of a parallel run -- must keep its
 * full rule set. This test pins the marker semantics and that {@code MergeRule.isApplicable}
 * consults the marker of the goal's own proof. A full end-to-end test (a mergeable proof under
 * several workers) is deferred until the lock-narrowing step.
 *
 */
public class MergeRuleMultiThreadGuardTest {

    private static final Path TEST_RESOURCES_DIR =
        HelperClassForTests.TESTCASE_DIRECTORY.resolve("merge/");

    private static Proof loadDummyProof() {
        KeYEnvironment<?> env = Assertions.assertDoesNotThrow(
            () -> KeYEnvironment.load(TEST_RESOURCES_DIR.resolve("dummy.key")));
        Proof proof = env.getLoadedProof();
        assertNotNull(proof);
        return proof;
    }

    @Test
    void runScopeIsPerProofAndBalances() {
        final Proof a = loadDummyProof();
        final Proof b = loadDummyProof();
        try {
            assertFalse(ParallelProver.isMultiThreadedRunActive(), "must be inactive by default");

            try (var scopeA = ParallelProver.enterMultiThreadedRun(a)) {
                assertTrue(ParallelProver.isMultiThreadedRunActive(a));
                assertFalse(ParallelProver.isMultiThreadedRunActive(b),
                    "a run on proof A must not mark proof B: B may be proved single-core "
                        + "in parallel and keeps its full rule set");
                assertTrue(ParallelProver.isMultiThreadedRunActive(),
                    "the coarse any-run query sees the run on A");

                try (var nested = ParallelProver.enterMultiThreadedRun(a)) {
                    assertTrue(ParallelProver.isMultiThreadedRunActive(a),
                        "nested scope on the same proof still active");
                }
                assertTrue(ParallelProver.isMultiThreadedRunActive(a),
                    "outer scope keeps proof A active after the nested scope closes");

                try (var scopeB = ParallelProver.enterMultiThreadedRun(b)) {
                    assertTrue(ParallelProver.isMultiThreadedRunActive(b),
                        "independent scopes for independent proofs");
                }
                assertFalse(ParallelProver.isMultiThreadedRunActive(b));
                assertTrue(ParallelProver.isMultiThreadedRunActive(a));
            }
            assertFalse(ParallelProver.isMultiThreadedRunActive(),
                "must be inactive after all scopes");
        } finally {
            a.dispose();
            b.dispose();
        }
    }

    @Test
    void mergeRuleIsDisabledOnlyOnTheProofWithTheActiveRun() {
        final Proof a = loadDummyProof();
        final Proof b = loadDummyProof();
        try {
            final Goal goalA = a.openGoals().head();
            final Goal goalB = b.openGoals().head();
            assertNotNull(goalA);
            assertNotNull(goalB);

            try (var scope = ParallelProver.enterMultiThreadedRun(a)) {
                // the guard short-circuits on A before touching the position, so null is safe
                assertFalse(MergeRule.INSTANCE.isApplicable(goalA, null),
                    "MergeRule must be inapplicable while a multi-worker run is active "
                        + "on the goal's proof");
                assertFalse(ParallelProver.isMultiThreadedRunActive(goalB.proof()),
                    "the guard on proof B must not fire: its marker is inactive, so "
                        + "MergeRule.isApplicable(goalB, pio) proceeds to the normal "
                        + "admissibility check");
            }
            assertFalse(ParallelProver.isMultiThreadedRunActive());
        } finally {
            a.dispose();
            b.dispose();
        }
    }
}
