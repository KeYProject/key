/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.net.URL;
import java.nio.file.Path;
import java.nio.file.Paths;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.prover.impl.ParallelProver;
import de.uka.ilkd.key.util.ProofStarter;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Stress test for the goal-level parallel prover once rule selection runs <em>outside</em> the
 * commit lock (i.e. matching/cost truly run concurrently). A correctness bug there is typically
 * nondeterministic, so a single run is not enough: this repeats high-worker-count proofs many times
 * and asserts each one still closes and stays equivalent (modulo branch order) to the
 * single-threaded proof.
 *
 * <p>
 * The problems chosen each stress a different concurrent surface: {@code prop_split} (independent
 * branches), {@code fol_split_skolem} (concurrent fresh-name minting across branches), and
 * {@code arith_poly} (the eviction/history-sensitive arithmetic caches).
 *
 * @author Claude (KeY multithreading effort)
 */
public class ConcurrentMatchingStressTest {

    private static final int WORKERS = 8;
    private static final int ITERATIONS = 30;

    @ParameterizedTest(name = "stress {0}")
    @ValueSource(strings = { "prop_split.key", "fol_split_skolem.key", "arith_poly.key" })
    void repeatedMultiWorkerRunsStayEquivalent(String file) throws Exception {
        ProofFingerprint baseline = prove(file, false);
        assertTrue(baseline.closed, () -> file + " did not close single-threaded");

        String prevEnabled = System.getProperty(ParallelProver.PARALLEL_PROPERTY);
        String prevThreads = System.getProperty(ParallelProver.THREADS_PROPERTY);
        System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
        System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(WORKERS));
        try {
            for (int i = 0; i < ITERATIONS; i++) {
                ProofFingerprint parallel = prove(file, true);
                final int iter = i;
                assertTrue(parallel.closed,
                    () -> file + " did not close on parallel iteration " + iter + ": " + parallel);
                assertTrue(baseline.equalsModuloOrder(parallel),
                    () -> file + " diverged on parallel iteration " + iter + ":\n  baseline="
                        + baseline + "\n  parallel=" + parallel);
            }
        } finally {
            restore(ParallelProver.PARALLEL_PROPERTY, prevEnabled);
            restore(ParallelProver.THREADS_PROPERTY, prevThreads);
        }
    }

    private static ProofFingerprint prove(String file, boolean parallel) throws Exception {
        URL url = ConcurrentMatchingStressTest.class
                .getResource("/de/uka/ilkd/key/prover/mt/equiv/" + file);
        Path keyFile = Paths.get(url.toURI());
        KeYEnvironment<?> env =
            KeYEnvironment.load(JavaProfile.getDefaultInstance(), keyFile, null, null, null, true);
        try {
            Proof proof = env.getLoadedProof();
            ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            starter.start();
            return ProofFingerprint.of(proof);
        } finally {
            env.dispose();
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
