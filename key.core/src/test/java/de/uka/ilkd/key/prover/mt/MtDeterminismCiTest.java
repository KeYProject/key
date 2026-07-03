/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ParallelProver;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIfSystemProperty;

import static org.junit.jupiter.api.Assertions.*;

/**
 * CI regression gate for the multi-core prover's <em>determinism</em> guarantee (the counterpart of
 * the {@code MtVarianceBenchmark}, which only measures). On the two proofs that historically
 * carried the residual run-to-run wobble -- {@code SimplifiedLinkedList.remove} (the queue/veto
 * channels) and {@code symmArray} (the fresh-naming channel, #3851) -- it asserts that
 * <ul>
 * <li>every repetition at {@value #WORKERS} workers builds a proof of the <em>same</em> size
 * (run-to-run bit-stability: no dependence on the worker schedule), and</li>
 * <li>that size equals the sequential proof's (the multi-core prover does not change the proof).
 * </li>
 * </ul>
 *
 * <p>
 * The worker count is set through {@link ParallelProver#THREADS_PROPERTY}, which is honoured
 * exactly (no clamp to the available processors), so the run is genuinely multi-worker even on a
 * low-core CI runner; the test asserts {@code > 1} effective workers so it can never pass by
 * silently degrading to single-core. Slow (a few large proofs, several times); gated with the
 * other stress gates and run by the {@code testMtStress} CI job.
 */
@EnabledIfSystemProperty(named = "key.mt.stress", matches = "true")
public class MtDeterminismCiTest {

    private static final int WORKERS = 4;
    private static final int REPS = 3;
    private static final int MAX_STEPS = 200000;

    /** Bit-stable, sequential-equivalent proofs, one representative of each residual channel. */
    private static final String[] PROOFS = {
        "heap/list_seq/SimplifiedLinkedList.remove.key",
        "standard_key/java_dl/symmArray.key",
    };

    private static String settingsSnapshot;

    @BeforeAll
    public static void snapshotSettings() {
        settingsSnapshot = ProofSettings.DEFAULT_SETTINGS.settingsToString();
    }

    @AfterAll
    public static void restoreSettings() {
        if (settingsSnapshot != null) {
            ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(settingsSnapshot);
        }
    }

    @Test
    public void proofsAreBitStableAtFourWorkersAndEqualTheSequentialProof() throws Exception {
        final Path examples = FindResources.getExampleDirectory();
        assertNotNull(examples, "examples directory not found");
        for (final String rel : PROOFS) {
            final Path keyFile = examples.resolve(rel);
            assertTrue(Files.exists(keyFile), () -> "missing example proof " + rel);

            final int seqNodes = prove(keyFile, 0);
            int firstMt = -1;
            for (int rep = 0; rep < REPS; rep++) {
                final int mtNodes = prove(keyFile, WORKERS);
                if (firstMt < 0) {
                    firstMt = mtNodes;
                }
                final int r = rep;
                final int expected = firstMt;
                assertEquals(expected, mtNodes,
                    () -> rel + ": " + WORKERS + "-worker proof size varied run-to-run (rep " + r
                        + " = " + mtNodes + ", first = " + expected
                        + ") -- proof search is not deterministic under the worker schedule");
            }
            final int mtNodes = firstMt;
            assertEquals(seqNodes, mtNodes,
                () -> rel + ": the " + WORKERS + "-worker proof (" + mtNodes + " nodes) differs "
                    + "from the sequential proof (" + seqNodes
                    + " nodes) -- the multi-core prover changed the proof");
        }
    }

    /**
     * Proves the file once; {@code workers == 0} means the sequential prover. Returns node count.
     */
    private int prove(Path keyFile, int workers) throws Exception {
        final String prevEnabled = System.getProperty(ParallelProver.PARALLEL_PROPERTY);
        final String prevThreads = System.getProperty(ParallelProver.THREADS_PROPERTY);
        if (workers > 0) {
            System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
            System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(workers));
            // guard against a silently single-core run: the parallel prover must actually be
            // selected, and the worker count is honoured exactly (no clamp to available cores), so
            // WORKERS workers really run even on a low-core CI machine
            assertTrue(ParallelProver.isEnabled(),
                "parallel prover must be enabled for the multi-worker run");
            assertEquals(workers, ParallelProver.effectiveWorkerCount(),
                "the multi-worker run must use exactly the requested worker count");
            assertTrue(ParallelProver.effectiveWorkerCount() > 1,
                "the determinism test is only meaningful with more than one worker");
        } else {
            System.setProperty(ParallelProver.PARALLEL_PROPERTY, "false");
        }
        ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(settingsSnapshot);
        final KeYEnvironment<?> env = KeYEnvironment.load(keyFile);
        try {
            final Proof proof = env.getLoadedProof();
            final ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            starter.setMaxRuleApplications(MAX_STEPS);
            starter.start();
            assertTrue(proof.closed(),
                () -> keyFile + " did not close with " + workers + " workers (open goals="
                    + proof.openGoals().size() + ")");
            return proof.countNodes();
        } finally {
            restore(ParallelProver.PARALLEL_PROPERTY, prevEnabled);
            restore(ParallelProver.THREADS_PROPERTY, prevThreads);
            env.dispose();
        }
    }

    private static void restore(String key, String value) {
        if (value == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, value);
        }
    }
}
