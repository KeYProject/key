/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ParallelProver;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.condition.EnabledIfSystemProperty;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

/**
 * Regression stress test for the goal-level parallel prover: a guard against reintroducing a
 * concurrency bug that makes proofs nondeterministically <em>fail to close</em> under more than one
 * worker.
 *
 * <p>
 * The unit-level {@link RealProofMtEquivalenceTest} gate uses small proofs at a few workers and one
 * run each, which is too tame to surface such races (the one that motivated this test &mdash; a
 * shared mutable key in the taclet-index cache, see {@code PrefixTermTacletAppIndexCacheImpl}
 * &mdash; showed up only on large <em>splitting</em> proofs with array/arithmetic reasoning at high
 * worker counts, and even then only ~50% of runs). This test deliberately uses exactly that shape:
 * a few large splitting proofs, run at a high (intentionally over-subscribed) worker count, several
 * times each, asserting that <b>every</b> run closes. A reintroduced race shows up as a run that
 * leaves the proof open.
 *
 * <p>
 * It is slow (minutes) and therefore gated by {@code -Dkey.mt.stress=true}; CI runs it via the
 * dedicated {@code testMtStress} Gradle task, not in the fast unit-test suite. The worker count is
 * deliberately not capped at the available cores: over-subscription increases thread interleaving,
 * which makes a race <em>more</em> likely to be caught on the few-core CI runners.
 *
 * @author Claude (KeY multithreading effort)
 */
@EnabledIfSystemProperty(named = "key.mt.stress", matches = "true")
public class MtStressTest {

    @ParameterizedTest(name = "{0} ({1} reps @ {2} workers)")
    @CsvSource({
        "standard_key/java_dl/symmArray.key, 8, 8",
        "heap/list_seq/SimplifiedLinkedList.remove.key, 3, 8",
    })
    void splittingProofClosesEveryRunInParallel(String relPath, int reps, int workers)
            throws Exception {
        final Path examples = FindResources.getExampleDirectory();
        assumeTrue(examples != null, "examples directory not found");
        final Path keyFile = examples.resolve(relPath);
        assertTrue(Files.exists(keyFile), () -> "missing example proof " + relPath);

        final String prevEnabled = System.getProperty(ParallelProver.PARALLEL_PROPERTY);
        final String prevThreads = System.getProperty(ParallelProver.THREADS_PROPERTY);
        System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
        System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(workers));
        try {
            for (int i = 0; i < reps; i++) {
                final int rep = i;
                final KeYEnvironment<?> env = KeYEnvironment.load(keyFile);
                try {
                    final Proof proof = env.getLoadedProof();
                    final ProofStarter starter = new ProofStarter(false);
                    starter.init(proof);
                    starter.start();
                    assertTrue(proof.closed(),
                        () -> relPath + " did not close on rep " + rep + " with " + workers
                            + " workers (open goals=" + proof.openGoals().size()
                            + "). This proof closes single-threaded, so a parallel run leaving it"
                            + " open means a reintroduced concurrency race.");
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
