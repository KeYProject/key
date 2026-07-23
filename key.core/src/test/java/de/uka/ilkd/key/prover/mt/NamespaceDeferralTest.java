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

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Verifies the namespace flush-deferral of the multi-worker run.
 *
 * <p>
 * During a multi-worker run, fresh symbols are kept node-local instead of being flushed into the
 * shared proof namespace (so that namespace can later stay immutable while matching moves out of
 * the
 * commit lock). Single-threaded proving also keeps proving-time symbols in the local namespace
 * layers (the flush targets a local copy, not the global {@code Services} namespace), so deferral
 * must leave the <em>global</em> namespace exactly as single-threaded proving does. This test pins
 * that invariant: a multi-worker run adds the same number of functions to the global namespace as a
 * single-threaded run of the same skolemizing, splitting problem.
 *
 */
public class NamespaceDeferralTest {

    /** Splits into independent branches AND skolemizes in each, so fresh functions are minted. */
    private static final String FILE = "fol_split_skolem.key";

    @Test
    void deferralLeavesGlobalNamespaceIdenticalToSingleThreaded() throws Exception {
        int singleThreadedNewFunctions = proveAndCountNewFunctions(1, false);
        int multiWorkerNewFunctions = proveAndCountNewFunctions(4, true);

        assertEquals(singleThreadedNewFunctions, multiWorkerNewFunctions,
            "multi-worker deferral changed how many functions end up in the global namespace "
                + "compared to single-threaded proving");
    }

    /**
     * Proves {@link #FILE} and returns how many functions the run added to the shared proof
     * namespace.
     *
     * @param threads worker count
     * @param parallel whether to enable the parallel prover
     */
    private static int proveAndCountNewFunctions(int threads, boolean parallel) throws Exception {
        KeYEnvironment<?> env = KeYEnvironment.load(JavaProfile.getDefaultInstance(), corpusFile(),
            null, null, null, true);
        String prevEnabled = System.getProperty(ParallelProver.PARALLEL_PROPERTY);
        String prevThreads = System.getProperty(ParallelProver.THREADS_PROPERTY);
        try {
            Proof proof = env.getLoadedProof();
            assertNotNull(proof);
            int before = proof.getServices().getNamespaces().functions().elements().size();

            if (parallel) {
                System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
                System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(threads));
                MtSwitch.assertParallelActive(threads);
            } else {
                MtSwitch.assertSingleThreaded();
            }
            ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            starter.start();

            assertTrue(proof.closed(), "proof did not close");
            int after = proof.getServices().getNamespaces().functions().elements().size();
            return after - before;
        } finally {
            restore(ParallelProver.PARALLEL_PROPERTY, prevEnabled);
            restore(ParallelProver.THREADS_PROPERTY, prevThreads);
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

    private static Path corpusFile() throws Exception {
        URL url = NamespaceDeferralTest.class.getResource(
            "/de/uka/ilkd/key/prover/mt/equiv/" + FILE);
        assertNotNull(url, () -> "Corpus file not on classpath: " + FILE);
        return Paths.get(url.toURI());
    }
}
