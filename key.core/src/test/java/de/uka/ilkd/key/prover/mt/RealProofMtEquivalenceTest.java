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
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Equivalence gate over a curated set of <em>real</em> proofs from {@code key.ui/examples} (drawn
 * from the {@code RunAllProofs} functional collection), for the goal-level multithreading effort.
 *
 * <p>
 * Unlike the hand-written synthetic corpus, these exercise actual Java-DL / heap / arithmetic proof
 * search. The set deliberately mixes <b>provable</b> problems (must close) with <b>not-provable</b>
 * ones (must <em>not</em> close &mdash; the suite tests that proofs do not accidentally close).
 *
 * <p>
 * <b>What is (and is not) asserted.</b> The gate asserts <b>soundness</b>: the parallel run reaches
 * the same closed/open <em>status</em> as expected (and as single-threaded). It does <em>not</em>
 * require an identical proof tree. Real proofs legitimately diverge under parallel search because
 * KeY's strategy cost is order/age-dependent (rule-app age, and fresh names are worker-tagged), so
 * processing goals in a different order &mdash; which the scheduler does even with a single worker,
 * and which thread interleaving does non-deterministically with several &mdash; yields a different
 * but equally valid proof. (Measured on {@code sum0.key}: single 297 nodes, parallel 295&ndash;296,
 * varying run to run; all closed.) Identity holds only for order-insensitive problems like the
 * synthetic corpus in {@link ProofEquivalenceTest}, which keeps the stricter check.
 *
 * <p>
 * These are kept small/fast so the gate is CI-friendly. Speedup and scaling on the largest proofs
 * are a separate, manual concern.
 *
 * @author Claude (KeY multithreading effort)
 */
public class RealProofMtEquivalenceTest {

    private static final int WORKERS = 4;

    /**
     * Loading the example proofs mutates the global {@link ProofSettings#DEFAULT_SETTINGS} (KeY
     * applies a problem's embedded settings on load). Snapshot it before and restore it after so
     * the
     * gate does not leak settings into later tests that share the JVM.
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
     * Curated {@code path, provable} rows. Paths are relative to {@code key.ui/examples}. {@code
     * provable=true} means the proof must close; {@code false} means it must stay open.
     */
    @ParameterizedTest(name = "{0} (provable={1})")
    @CsvSource({
        // provable (must close)
        "standard_key/BookExamples/02FirstOrderLogic/Ex2.58.key, true",
        "standard_key/BookExamples/03DynamicLogic/Sect3.3.1.key, true",
        "heap/comprehensions/sum0.key, true",
        // not provable (must NOT accidentally close, even under parallel search)
        "standard_key/prop_log/reallySimple.key, false",
        "standard_key/pred_log/sameName1.key, false",
        "standard_key/java_dl/danglingElse.key, false",
        "standard_key/java_dl/jml-min/min-unprovable1.key, false",
        "heap/polarity_tests/wellformed2.key, false",
    })
    void parallelMatchesSingleThreadedOnRealProof(String relPath, boolean provable)
            throws Exception {
        Path examples = FindResources.getExampleDirectory();
        Assumptions.assumeTrue(examples != null, "examples directory not found");
        Path keyFile = examples.resolve(relPath);
        Assumptions.assumeTrue(Files.exists(keyFile), () -> "missing example: " + keyFile);

        ProofFingerprint single = prove(keyFile, false);
        ProofFingerprint parallel = prove(keyFile, true);

        // Soundness: the closed/open status matches RunAllProofs' expectation in both modes.
        // (A provable problem must close; a not-provable one must not accidentally close.)
        assertEquals(provable, single.closed,
            () -> relPath + " single-threaded closed=" + single.closed + " expected " + provable);
        assertEquals(provable, parallel.closed,
            () -> relPath + " parallel closed=" + parallel.closed + " expected " + provable);
        // The proof trees may differ (order/age-dependent strategy cost) -- that is expected and
        // sound; we deliberately do NOT assert fingerprint equality here.
    }

    private static ProofFingerprint prove(Path keyFile, boolean parallel) throws Exception {
        KeYEnvironment<?> env = KeYEnvironment.load(keyFile);
        String prevEnabled = System.getProperty(ParallelProver.PARALLEL_PROPERTY);
        String prevThreads = System.getProperty(ParallelProver.THREADS_PROPERTY);
        if (parallel) {
            System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
            System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(WORKERS));
        }
        try {
            Proof proof = env.getLoadedProof();
            assertNotNull(proof, () -> "no proof loaded for " + keyFile);
            ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            starter.start();
            return ProofFingerprint.of(proof);
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
}
