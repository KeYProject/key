/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import de.uka.ilkd.key.prover.impl.ParallelProver;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Checks, for a test that means to prove on a particular prover, that the prover it asked for is
 * the one it actually gets.
 * <p>
 * Which prover an automatic proof search uses is not passed to it as an argument: it is read off
 * the settings and the system properties when the search starts (see
 * {@link ParallelProver#isEnabled()}).
 * A test therefore selects its prover by setting those, which is easy to get wrong in a way nothing
 * notices: the whole test suite is pinned to the single-threaded prover (see the root build file),
 * so a multi-core test whose switch does not take effect does not fail, it quietly proves
 * single-threaded and passes -- and then asserts nothing about the multi-core prover at all. The
 * checks here turn that into a failure.
 */
final class MtSwitch {

    private MtSwitch() {
    }

    /**
     * Checks that a run started now would use the multi-core prover with {@code workers} workers.
     * Call after selecting the multi-core prover, before proving.
     *
     * @param workers the number of workers the test means to prove with
     */
    static void assertParallelActive(int workers) {
        assertTrue(ParallelProver.isEnabled(),
            "this test proves on the multi-core prover, but the prover selection says otherwise: "
                + "the run would be single-threaded and the test would assert nothing");
        assertEquals(workers, ParallelProver.effectiveWorkerCount(),
            "this test proves with " + workers + " workers, but a run started now would use "
                + ParallelProver.effectiveWorkerCount());
    }

    /**
     * Checks that a run started now would use the multi-core prover with more than one worker, for
     * tests that only require the workers to be concurrent and do not fix their number.
     */
    static void assertMultiWorkerActive() {
        assertTrue(ParallelProver.isEnabled(),
            "this test proves on the multi-core prover, but the prover selection says otherwise: "
                + "the run would be single-threaded and the test would assert nothing");
        assertTrue(ParallelProver.effectiveWorkerCount() > 1,
            "this test needs concurrent workers, but a run started now would use only "
                + ParallelProver.effectiveWorkerCount());
    }

    /**
     * Checks that a run started now would use the single-threaded prover. Call after selecting it,
     * so that a test comparing against a single-threaded run cannot silently compare two multi-core
     * runs.
     */
    static void assertSingleThreaded() {
        assertFalse(ParallelProver.isEnabled(),
            "this test proves single-threaded, but the prover selection says the run would use the "
                + "multi-core prover");
    }
}
