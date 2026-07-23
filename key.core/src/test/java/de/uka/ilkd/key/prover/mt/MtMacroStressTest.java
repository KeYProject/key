/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.FinishSymbolicExecutionMacro;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ParallelProver;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIfSystemProperty;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

/**
 * Stress tests for tree-shrinking mutations and macro filter strategies under the multi-core
 * prover.
 *
 * <p>
 * The first scenario guards pruning a subtree that was <em>produced by many workers</em>: a
 * parallel run is stopped by a tiny step budget, the resulting partial subtree is pruned back to
 * the root, and a second parallel run must then close the proof &mdash; a corrupted tree from the
 * prune would show up as an inconsistent goal set, a failure to close, or an exception.
 *
 * <p>
 * The second scenario runs {@link FinishSymbolicExecutionMacro} on the parallel prover: its filter
 * strategy consults a shared {@link de.uka.ilkd.key.macros.ModalityCache} from
 * {@code Strategy#isApprovedApp} on every worker, off the commit lock.
 *
 * <p>
 * Gated by {@code -Dkey.mt.stress}; runs via the {@code testMtStress} Gradle task.
 *
 */
@EnabledIfSystemProperty(named = "key.mt.stress", matches = "true")
public class MtMacroStressTest {

    private static final String PROOF = "standard_key/java_dl/symmArray.key";
    private static final int WORKERS = 8;
    private static final int REPS = 3;
    private static final int TINY_BUDGET = 50;
    private static final int SE_REPS = 5;

    /**
     * Step cap for the closing parallel runs. Generous on purpose: parallel goal-order divergence
     * can make a run explore more than the single-threaded proof needs, so a modest cap would
     * occasionally be exhausted by a perfectly sound run. A real corruption leaves the proof
     * saturated-open well below this cap, so raising it absorbs benign divergence without masking
     * a bug.
     */
    private static final int MAX_STEPS = 200_000;

    /**
     * Loading an example applies its embedded settings to the global
     * {@link ProofSettings#DEFAULT_SETTINGS}; snapshot and restore them so they neither leak into
     * tests run later in the same JVM nor differ between the repetitions here.
     */
    private static String settingsSnapshot;

    @BeforeAll
    static void snapshotSettings() {
        settingsSnapshot = ProofSettings.DEFAULT_SETTINGS.settingsToString();
    }

    @AfterAll
    static void restoreSettings() {
        ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(settingsSnapshot);
    }

    /**
     * Each repetition: run the parallel prover with a tiny step budget at a high worker count
     * (produces a partial, many-worker-built subtree), prune that subtree back to the root, assert
     * the goal set is consistent, then run the parallel prover to completion and assert the proof
     * closes, which proves that the prune left a consistent, completable tree.
     */
    @Test
    void pruneOfParallelSubtreeStaysSafeUnderManyWorkers() throws Exception {
        final Path examples = FindResources.getExampleDirectory();
        assumeTrue(examples != null, "examples directory not found");
        final Path keyFile = examples.resolve(PROOF);
        assertTrue(Files.exists(keyFile), () -> "missing example proof " + PROOF);

        final String prevEnabled = System.getProperty(ParallelProver.PARALLEL_PROPERTY);
        final String prevThreads = System.getProperty(ParallelProver.THREADS_PROPERTY);
        System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
        System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(WORKERS));
        try {
            for (int rep = 0; rep < REPS; rep++) {
                final int r = rep;
                ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(settingsSnapshot);
                final KeYEnvironment<?> env = KeYEnvironment.load(keyFile);
                try {
                    final Proof proof = env.getLoadedProof();

                    // Tiny budget: the parallel run cannot close this proof, leaving a partial
                    // subtree built by many workers.
                    final ProofStarter partial = new ProofStarter(false);
                    partial.init(proof);
                    partial.setMaxRuleApplications(TINY_BUDGET);
                    partial.start();
                    assertFalse(proof.closed(),
                        () -> PROOF + " unexpectedly closed within " + TINY_BUDGET
                            + " steps (rep " + r + ")");
                    assertTrue(proof.countNodes() > 1,
                        () -> "the budgeted parallel run made no progress (rep " + r + ")");

                    // Prune the parallel subtree -- the tree-shrinking mutation under guard.
                    proof.pruneProof(proof.root());
                    assertEquals(1, proof.openGoals().size(),
                        () -> "pruning the parallel subtree corrupted the goal set (rep " + r
                            + ")");

                    // Full budget: a parallel run must now close the proof, proving the prune
                    // left a consistent, completable tree.
                    final ProofStarter closer = new ProofStarter(false);
                    closer.init(proof);
                    closer.setMaxRuleApplications(MAX_STEPS);
                    closer.start();
                    assertTrue(proof.closed(),
                        () -> PROOF + " did not close after pruning the parallel subtree (rep " + r
                            + ") -- likely tree corruption from the prune");
                } finally {
                    env.dispose();
                }
            }
        } finally {
            restore(ParallelProver.PARALLEL_PROPERTY, prevEnabled);
            restore(ParallelProver.THREADS_PROPERTY, prevThreads);
        }
    }

    /**
     * Finish symbolic execution under the multi-core prover. The macro's filter strategy
     * ({@code FinishSymbolicExecutionMacro.FilterSymbexStrategy}) consults a shared
     * {@link de.uka.ilkd.key.macros.ModalityCache} from {@code Strategy#isApprovedApp} on every
     * worker, off the commit lock -- so a cache race would corrupt its bounded cache or mis-report
     * modality presence and leave SE unfinished. The number of open goals after SE is fixed by the
     * program's execution-path structure, so it must be identical across reps regardless of worker
     * scheduling; a differing count means a race left symbolic execution inconsistent.
     */
    @Test
    void finishSymbolicExecutionStaysSafeUnderManyWorkers() throws Exception {
        final Path examples = FindResources.getExampleDirectory();
        assumeTrue(examples != null, "examples directory not found");
        final Path keyFile = examples.resolve(PROOF);
        assertTrue(Files.exists(keyFile), () -> "missing example proof " + PROOF);

        final String prevEnabled = System.getProperty(ParallelProver.PARALLEL_PROPERTY);
        final String prevThreads = System.getProperty(ParallelProver.THREADS_PROPERTY);
        System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
        System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(WORKERS));
        try {
            int firstOpenGoals = -1;
            for (int rep = 0; rep < SE_REPS; rep++) {
                final int r = rep;
                ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(settingsSnapshot);
                final KeYEnvironment<?> env = KeYEnvironment.load(keyFile);
                try {
                    final Proof proof = env.getLoadedProof();
                    new FinishSymbolicExecutionMacro().applyTo(null, proof.root(), null, null);
                    assertTrue(proof.countNodes() > 1,
                        () -> "finishSymbolicExecution made no progress (rep " + r + ")");
                    final int open = proof.openGoals().size();
                    if (firstOpenGoals < 0) {
                        firstOpenGoals = open;
                    } else {
                        assertEquals(firstOpenGoals, open,
                            PROOF + ": open-goal count after finishSymbolicExecution differs across"
                                + " reps (rep " + r + ": " + open + " vs " + firstOpenGoals
                                + ") -- a ModalityCache race under the multi-core prover left"
                                + " symbolic execution in an inconsistent state");
                    }
                } finally {
                    env.dispose();
                }
            }
        } finally {
            restore(ParallelProver.PARALLEL_PROPERTY, prevEnabled);
            restore(ParallelProver.THREADS_PROPERTY, prevThreads);
        }
    }

    private static void restore(String key, String previous) {
        if (previous == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, previous);
        }
    }
}
