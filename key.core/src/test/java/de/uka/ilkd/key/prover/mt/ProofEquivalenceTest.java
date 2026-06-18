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
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.util.ProofStarter;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The equivalence gate for the goal-level parallel prover.
 *
 * <p>
 * The gate runs each problem in the corpus and asserts {@link ProofFingerprint}s agree across
 * configurations:
 * <ol>
 * <li>{@link #singleThreadedIsDeterministic} &mdash; automatic search is bit-for-bit reproducible
 * across runs (the property a parallel run must preserve);
 * <li>{@link #parallelMatchesSingleThreaded} &mdash; the {@code ParallelProver} with one worker
 * produces a proof equivalent (modulo branch order) to {@code ApplyStrategy};
 * <li>{@link #multiWorkerMatchesSingleThreaded} &mdash; the {@code ParallelProver} with several
 * workers does too.
 * </ol>
 * Equivalence "modulo order" is used for the parallel comparisons because independent branches may
 * be scheduled differently; the strict single-threaded determinism check stays as the baseline.
 *
 */
public class ProofEquivalenceTest {

    /** Classpath-relative directory holding the corpus {@code .key} files. */
    private static final String CORPUS_DIR = "/de/uka/ilkd/key/prover/mt/equiv/";

    /**
     * Loading the corpus mutates the global {@link ProofSettings#DEFAULT_SETTINGS} (KeY applies a
     * problem's embedded settings on load). Snapshot it before and restore it after so the gate
     * does
     * not leak settings into later tests that share the JVM.
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

    /** The corpus. Small, fast, deterministic problems with non-trivial proof trees. */
    private static final String[] CORPUS =
        { "prop_chain.key", "prop_split.key", "fol_quant.key", "fol_split_skolem.key",
            "arith_poly.key" };

    /** Single source of truth for the parameterized gates; see {@link #CORPUS}. */
    static String[] corpus() {
        return CORPUS;
    }

    @ParameterizedTest(name = "deterministic: {0}")
    @MethodSource("corpus")
    void singleThreadedIsDeterministic(String file) throws Exception {
        ProofFingerprint first = proveAndFingerprint(file);
        ProofFingerprint second = proveAndFingerprint(file);

        assertTrue(first.closed, () -> file + " did not close on the first run: " + first);
        assertTrue(second.closed, () -> file + " did not close on the second run: " + second);
        // Strict equality, including the scheduling-sensitive ordered digest: single-threaded
        // search must be bit-for-bit reproducible.
        assertEquals(first, second,
            () -> "Non-deterministic proof for " + file + ":\n  run1=" + first + "\n  run2="
                + second);
    }

    /**
     * The goal-level parallelism gate with a single worker. The proof produced by the
     * {@code ParallelProver} (selected via {@code -Dkey.prover.parallel}) must be equivalent up to
     * branch order to the single-threaded one.
     */
    @ParameterizedTest(name = "parallel==single: {0}")
    @MethodSource("corpus")
    void parallelMatchesSingleThreaded(String file) throws Exception {
        assertParallelMatchesSingle(file, 1);
    }

    /**
     * The same gate with multiple worker threads: real goal-level parallelism (modulo the current
     * coarse commit lock) must still produce a proof equivalent to the single-threaded one.
     */
    @ParameterizedTest(name = "parallel(4)==single: {0}")
    @MethodSource("corpus")
    void multiWorkerMatchesSingleThreaded(String file) throws Exception {
        assertParallelMatchesSingle(file, 4);
    }

    /**
     * Proves {@code file} single-threaded and with {@code threads} workers; asserts equivalence.
     */
    private static void assertParallelMatchesSingle(String file, int threads) throws Exception {
        ProofFingerprint single = proveAndFingerprint(file);

        ProofFingerprint parallel;
        String prevEnabled = System.getProperty(ParallelProver.PARALLEL_PROPERTY);
        String prevThreads = System.getProperty(ParallelProver.THREADS_PROPERTY);
        System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
        System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(threads));
        try {
            parallel = proveAndFingerprint(file);
        } finally {
            restore(ParallelProver.PARALLEL_PROPERTY, prevEnabled);
            restore(ParallelProver.THREADS_PROPERTY, prevThreads);
        }

        assertTrue(single.closed, () -> file + " did not close single-threaded: " + single);
        assertTrue(parallel.closed,
            () -> file + " did not close with " + threads + " workers: " + parallel);
        assertTrue(single.equalsModuloOrder(parallel),
            () -> "Parallel run (" + threads + " workers) diverged from single-threaded for " + file
                + ":\n  single=" + single + "\n  parallel=" + parallel);
    }

    private static void restore(String key, String previous) {
        if (previous == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, previous);
        }
    }

    /**
     * Guards against a degenerate fingerprint. The equivalence gate is only meaningful if the
     * fingerprint actually distinguishes different proofs and reflects non-trivial trees, so we
     * assert the corpus produces distinct fingerprints with more than one node each.
     */
    @Test
    void fingerprintIsDiscriminating() throws Exception {
        var seen = new java.util.HashSet<String>();
        for (String file : CORPUS) {
            ProofFingerprint fp = proveAndFingerprint(file);
            assertTrue(fp.nodeCount > 1, () -> file + " produced a trivial proof tree: " + fp);
            assertTrue(seen.add(fp.canonicalDigest),
                () -> "Duplicate canonical digest for " + file
                    + " (fingerprint not discriminating)");
        }
    }

    /**
     * Loads a corpus problem, runs automatic proof search to completion, returns its fingerprint.
     */
    private static ProofFingerprint proveAndFingerprint(String file) throws Exception {
        Path keyFile = corpusFile(file);
        KeYEnvironment<?> env =
            KeYEnvironment.load(JavaProfile.getDefaultInstance(), keyFile, null, null, null, true);
        try {
            Proof proof = env.getLoadedProof();
            assertNotNull(proof, () -> "No proof loaded for " + file);

            ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            starter.start();

            return ProofFingerprint.of(proof);
        } finally {
            env.dispose();
        }
    }

    private static Path corpusFile(String file) throws Exception {
        URL url = ProofEquivalenceTest.class.getResource(CORPUS_DIR + file);
        assertNotNull(url, () -> "Corpus file not on classpath: " + CORPUS_DIR + file);
        return Paths.get(url.toURI());
    }
}
