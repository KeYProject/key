/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.net.URL;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.concurrent.atomic.AtomicInteger;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.EssentialProofListener;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.util.ProofStarter;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests the deregistration foundation ({@link Proof#suspendNonEssentialListeners()}) for the
 * goal-level multithreading effort.
 *
 * <p>
 * Verifies the three properties the parallel prover will depend on:
 * <ol>
 * <li>non-essential observers do not fire while suspended, and fire again after restoration;
 * <li>{@link EssentialProofListener}s keep firing throughout a suspended run;
 * <li>suspending observers does not change the resulting proof (its {@link ProofFingerprint} is
 * identical with and without an observer attached during the run).
 * </ol>
 *
 * @author Claude (KeY multithreading effort)
 */
public class ListenerSuspensionTest {

    private static final String CORPUS_DIR = "/de/uka/ilkd/key/prover/mt/equiv/";

    /** A plain observer: counts rule-application events. Not marked essential. */
    private static final class CountingObserver implements RuleAppListener {
        final AtomicInteger count = new AtomicInteger();

        @Override
        public void ruleApplied(ProofEvent e) {
            count.incrementAndGet();
        }
    }

    /** An essential observer: same behaviour, but tagged so it survives suspension. */
    private static final class EssentialCountingObserver
            implements RuleAppListener, EssentialProofListener {
        final AtomicInteger count = new AtomicInteger();

        @Override
        public void ruleApplied(ProofEvent e) {
            count.incrementAndGet();
        }
    }

    /** A non-essential proof-tree observer: counts {@code proofClosed} events. */
    private static final class CountingTreeObserver extends ProofTreeAdapter {
        final AtomicInteger closedCount = new AtomicInteger();

        @Override
        public void proofClosed(ProofTreeEvent e) {
            closedCount.incrementAndGet();
        }
    }

    /**
     * If the proof closes while the listeners are suspended (as it does on the multi-core prover),
     * the {@code proofClosed} event must be re-delivered to the suspended listeners when the
     * suspension scope closes -- otherwise the GUI's "proof closed" notification never appears.
     */
    @Test
    void proofClosedIsRedeliveredToSuspendedListenersAfterTheRun() throws Exception {
        KeYEnvironment<?> env = load("prop_chain.key");
        try {
            Proof proof = env.getLoadedProof();
            CountingTreeObserver observer = new CountingTreeObserver();
            proof.addProofTreeListener(observer);

            try (var ignored = proof.suspendNonEssentialListeners()) {
                runToCompletion(proof); // closes the proof while the listener is suspended
                assertEquals(0, observer.closedCount.get(),
                    "proofClosed reached the listener while it should have been suspended");
            }

            assertTrue(proof.closed(), "proof did not close");
            assertEquals(1, observer.closedCount.get(),
                "proofClosed was not re-delivered to the suspended listener after the run");
        } finally {
            env.dispose();
        }
    }

    @Test
    void nonEssentialObserverIsSilencedWhileSuspended() throws Exception {
        KeYEnvironment<?> env = load("prop_chain.key");
        try {
            Proof proof = env.getLoadedProof();
            CountingObserver observer = new CountingObserver();
            proof.addRuleAppListener(observer);

            try (var ignored = proof.suspendNonEssentialListeners()) {
                runToCompletion(proof);
            }

            assertEquals(0, observer.count.get(),
                "non-essential observer fired while it should have been suspended");
            assertTrue(proof.closed(), "proof did not close");
        } finally {
            env.dispose();
        }
    }

    @Test
    void observerIsReattachedAfterSuspensionScope() throws Exception {
        KeYEnvironment<?> env = load("prop_chain.key");
        try {
            Proof proof = env.getLoadedProof();
            CountingObserver observer = new CountingObserver();
            proof.addRuleAppListener(observer);

            // Open and immediately close the suspension scope without proving: the observer must
            // be restored so that the subsequent (unsuspended) run delivers events to it.
            try (var ignored = proof.suspendNonEssentialListeners()) {
                // nothing proved here
            }
            runToCompletion(proof);

            assertTrue(proof.closed(), "proof did not close");
            assertTrue(observer.count.get() > 0,
                "observer was not re-attached after the suspension scope closed");
        } finally {
            env.dispose();
        }
    }

    @Test
    void essentialObserverKeepsFiringWhileSuspended() throws Exception {
        KeYEnvironment<?> env = load("prop_chain.key");
        try {
            Proof proof = env.getLoadedProof();
            EssentialCountingObserver essential = new EssentialCountingObserver();
            proof.addRuleAppListener(essential);

            try (var ignored = proof.suspendNonEssentialListeners()) {
                runToCompletion(proof);
            }

            assertTrue(proof.closed(), "proof did not close");
            assertTrue(essential.count.get() > 0,
                "essential observer was wrongly suspended (received no events)");
        } finally {
            env.dispose();
        }
    }

    @Test
    void suspendingObserversDoesNotChangeTheProof() throws Exception {
        // Baseline: prove with no extra observer attached.
        ProofFingerprint baseline;
        KeYEnvironment<?> env1 = load("prop_split.key");
        try {
            Proof proof = env1.getLoadedProof();
            try (var ignored = proof.suspendNonEssentialListeners()) {
                runToCompletion(proof);
            }
            baseline = ProofFingerprint.of(proof);
        } finally {
            env1.dispose();
        }

        // Same problem, but with a non-essential observer attached and then suspended for the run.
        ProofFingerprint withSuspendedObserver;
        KeYEnvironment<?> env2 = load("prop_split.key");
        try {
            Proof proof = env2.getLoadedProof();
            proof.addRuleAppListener(new CountingObserver());
            try (var ignored = proof.suspendNonEssentialListeners()) {
                runToCompletion(proof);
            }
            withSuspendedObserver = ProofFingerprint.of(proof);
        } finally {
            env2.dispose();
        }

        assertTrue(baseline.closed, "baseline proof did not close");
        assertEquals(baseline, withSuspendedObserver,
            () -> "suspending an observer changed the proof:\n  baseline=" + baseline
                + "\n  withObserver=" + withSuspendedObserver);
    }

    private static void runToCompletion(Proof proof) {
        ProofStarter starter = new ProofStarter(false);
        starter.init(proof);
        starter.start();
    }

    private static KeYEnvironment<?> load(String file) throws Exception {
        URL url = ListenerSuspensionTest.class.getResource(CORPUS_DIR + file);
        assertNotNull(url, () -> "Corpus file not on classpath: " + CORPUS_DIR + file);
        Path keyFile = Paths.get(url.toURI());
        return KeYEnvironment.load(JavaProfile.getDefaultInstance(), keyFile, null, null, null,
            true);
    }
}
