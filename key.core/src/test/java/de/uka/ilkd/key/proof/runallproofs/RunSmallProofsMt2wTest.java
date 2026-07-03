/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.runallproofs;

import java.io.IOException;
import java.util.stream.Stream;

import de.uka.ilkd.key.prover.impl.ParallelProver;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.TestFactory;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Runs a small curated proof set through the RunAllProofs machinery on the <em>multi-core</em>
 * prover with two workers, so CI exercises the parallel prover on the same framework the
 * single-core regression suite uses (as opposed to only the hand-written MT stress tests). The
 * two workers are set through {@link ParallelProver#THREADS_PROPERTY}, which is honoured exactly
 * (no clamp to available cores), so the run really is multi-worker even on a single-core runner.
 *
 * @see ProofCollections#smallMultiThreaded()
 * @see RunSmallProofsMt4wTest
 */
@Tag("slow")
@Tag("testRunAllProofs")
public final class RunSmallProofsMt2wTest {

    static final int WORKERS = 2;

    private static String prevEnabled;
    private static String prevThreads;

    @BeforeAll
    static void enableParallelProver() {
        prevEnabled = System.getProperty(ParallelProver.PARALLEL_PROPERTY);
        prevThreads = System.getProperty(ParallelProver.THREADS_PROPERTY);
        System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
        System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(WORKERS));
        assertTrue(ParallelProver.isEnabled(), "parallel prover must be enabled for this suite");
        assertEquals(WORKERS, ParallelProver.effectiveWorkerCount(),
            "this suite must genuinely run with " + WORKERS + " workers");
        assertTrue(ParallelProver.effectiveWorkerCount() > 1,
            "an MT suite that degrades to a single worker is not testing anything");
    }

    @AfterAll
    static void restoreParallelProver() {
        restore(ParallelProver.PARALLEL_PROPERTY, prevEnabled);
        restore(ParallelProver.THREADS_PROPERTY, prevThreads);
    }

    @TestFactory
    Stream<DynamicTest> data() throws IOException {
        var proofCollection = ProofCollections.smallMultiThreaded();
        proofCollection.getSettings().getStatisticsFile().setUp();
        return RunAllProofsTest.data(proofCollection);
    }

    private static void restore(String key, String value) {
        if (value == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, value);
        }
    }
}
