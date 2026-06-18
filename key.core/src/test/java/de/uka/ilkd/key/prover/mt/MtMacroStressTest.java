/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ParallelProver;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIfSystemProperty;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

/**
 * Stress test for proof macros under the multi-core prover, in particular the
 * {@link TryCloseMacro} prune path: when a try-close attempt does not close within its step budget,
 * the macro prunes the (parallel, partially explored) subtree it produced. That prune is a
 * tree-shrinking mutation, and this test guards that it stays safe and non-corrupting under many
 * workers &mdash; the macro routes through the parallel prover, whose {@code start()} only returns
 * once every worker has stopped, so the prune runs with no live workers.
 *
 * <p>
 * Each repetition: run try-close with a tiny budget at a high worker count (forces a prune of a
 * parallel subtree), assert the proof is back to open, then run try-close to completion (the
 * parallel macro close path) and assert it closes. A corrupted tree from the prune would show up as
 * a failure to close, an inconsistent goal set, or an exception. Gated by {@code -Dkey.mt.stress};
 * runs via the {@code testMtStress} Gradle task.
 *
 * @author Claude (KeY multithreading effort)
 */
@EnabledIfSystemProperty(named = "key.mt.stress", matches = "true")
public class MtMacroStressTest {

    private static final String PROOF = "standard_key/java_dl/symmArray.key";
    private static final int WORKERS = 8;
    private static final int REPS = 3;
    private static final int TINY_BUDGET = 50;

    @Test
    void tryCloseMacroPruneAndCloseStaySafeUnderManyWorkers() throws Exception {
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
                final KeYEnvironment<?> env = KeYEnvironment.load(keyFile);
                try {
                    final Proof proof = env.getLoadedProof();

                    // Tiny budget: the attempt cannot close this proof, so the macro prunes the
                    // (parallel) subtree it explored, restoring the open goal.
                    new TryCloseMacro(TINY_BUDGET).applyTo(null, proof.root(), null, null);
                    assertFalse(proof.closed(),
                        () -> PROOF + " unexpectedly closed within " + TINY_BUDGET
                            + " steps (rep " + r + ")");
                    assertTrue(proof.openGoals().size() >= 1,
                        () -> "no open goal after try-close prune (rep " + r
                            + ") -- the prune may have corrupted the tree");

                    // Full budget: the parallel macro close path must now close the (re-opened)
                    // proof, proving the earlier prune left a consistent, completable tree.
                    new TryCloseMacro().applyTo(null, proof.root(), null, null);
                    assertTrue(proof.closed(),
                        () -> PROOF + " did not close after try-close to completion (rep " + r
                            + ") -- likely tree corruption from a prune under the multi-core prover");
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
