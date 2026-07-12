/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.runallproofs;

import java.io.IOException;
import java.util.stream.Stream;

import de.uka.ilkd.key.prover.impl.ParallelProver;
import de.uka.ilkd.key.prover.mt.MtFailureAdvice;
import de.uka.ilkd.key.settings.ProofSettings;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.TestFactory;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Runs a small curated proof set through the RunAllProofs machinery on the <em>multi-core</em>
 * prover with four workers, so CI exercises the parallel prover on the same framework the
 * single-core regression suite uses (as opposed to only the hand-written MT stress tests). The
 * four workers are set through {@link ParallelProver#THREADS_PROPERTY}, which is honoured exactly
 * (no clamp to available cores), so the run really is multi-worker even on a single-core runner.
 *
 * @see ProofCollections#smallMultiThreadedSplitting()
 * @see RunSmallProofsMt2wTest
 */
@Tag("slow")
@Tag("owntest")
@Tag("testRunAllProofs")
public final class RunSmallProofsMt4wTest {

    static final int WORKERS = 4;

    private static String prevEnabled;
    private static String prevThreads;
    private static String settingsSnapshot;

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
        // RunAllProofs loads its own KeY settings into the shared ProofSettings.DEFAULT_SETTINGS;
        // snapshot it so this (NOFORK, in-JVM) suite cannot leak those settings to later tests.
        settingsSnapshot = ProofSettings.DEFAULT_SETTINGS.settingsToString();
    }

    @AfterAll
    static void restoreParallelProver() {
        if (settingsSnapshot != null) {
            ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(settingsSnapshot);
        }
        restore(ParallelProver.PARALLEL_PROPERTY, prevEnabled);
        restore(ParallelProver.THREADS_PROPERTY, prevThreads);
    }

    @TestFactory
    Stream<DynamicTest> data() throws IOException {
        var proofCollection = ProofCollections.smallMultiThreadedSplitting();
        proofCollection.getSettings().getStatisticsFile().setUp();
        // append the multi-core advice block to every failure, so a developer who has never
        // worked with the multi-core prover knows what to look for
        return RunAllProofsTest.data(proofCollection)
                .map(test -> DynamicTest.dynamicTest(test.getDisplayName(), () -> {
                    try {
                        test.getExecutable().execute();
                    } catch (AssertionError e) {
                        throw new AssertionError(e.getMessage() + MtFailureAdvice.mtCorpus(), e);
                    }
                }));
    }

    private static void restore(String key, String value) {
        if (value == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, value);
        }
    }
}
