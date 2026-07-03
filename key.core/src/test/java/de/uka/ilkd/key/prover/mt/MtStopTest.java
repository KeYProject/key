/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;
import java.util.stream.Collectors;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ParallelProver;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Regression test for the GUI freeze when the user stops a running multi-core auto-mode.
 *
 * <p>
 * Stopping auto mode interrupts the background thread running {@link ParallelProver#start}. The
 * bug:
 * the listener suspension (which detaches the Swing proof-tree listeners for the duration of the
 * run)
 * is a try-with-resources resource and was therefore restored <em>before</em> the worker pool was
 * shut down, and the shutdown did not wait for the workers. So {@code start()} returned while a
 * worker was still mid-step; that worker then delivered a {@code proofExpanded} event into the
 * now-live Swing {@code GUIProofTreeModel} off the EDT and deadlocked against it (the EDT held the
 * AWT tree lock and wanted the model monitor; the worker held the model monitor and wanted the AWT
 * tree lock).
 *
 * <p>
 * This headless test cannot involve Swing, so it asserts the invariant whose violation enabled the
 * deadlock: once {@code start()} returns after an interrupt, <em>no</em> parallel worker thread is
 * still alive. The fix waits for the pool to terminate while the listeners are still suspended, so
 * the property holds and the GUI listeners are only re-attached once the proof is quiescent.
 *
 * @author Claude (KeY multithreading effort)
 */
public class MtStopTest {

    /**
     * Loading the example applies its embedded settings to the global
     * {@link ProofSettings#DEFAULT_SETTINGS}; snapshot and restore them so they do not leak into
     * tests run later in the same JVM.
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

    @Test
    @Timeout(120)
    void interruptingTheRunLeavesNoWorkerAliveWhenStartReturns() throws Exception {
        // A real, sizeable proof so the run is still going when we interrupt it ~400 ms in.
        Path examples = FindResources.getExampleDirectory();
        Assumptions.assumeTrue(examples != null, "examples directory not found");
        Path keyFile = examples.resolve("standard_key/java_dl/symmArray.key");
        Assumptions.assumeTrue(Files.exists(keyFile), "symmArray example missing");

        String prevEnabled = System.getProperty(ParallelProver.PARALLEL_PROPERTY);
        String prevThreads = System.getProperty(ParallelProver.THREADS_PROPERTY);
        System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
        System.setProperty(ParallelProver.THREADS_PROPERTY, "4");

        KeYEnvironment<?> env = KeYEnvironment.load(keyFile);
        try {
            Proof proof = env.getLoadedProof();
            ProofStarter starter = new ProofStarter(false);
            starter.init(proof);

            AtomicReference<Throwable> failure = new AtomicReference<>();
            Thread driver = new Thread(() -> {
                try {
                    starter.start();
                } catch (Throwable t) {
                    failure.set(t);
                }
            }, "mt-stop-driver");
            driver.start();

            // Interrupt only once the parallel run is observably underway, so the stop lands
            // mid-run rather than (on a fast JVM) after the run has already finished -- which would
            // make the invariant below vacuous. isMultiThreadedRunActive() is a global marker set
            // for the whole multi-worker run (ParallelProver.enterMultiWorkerRunScope) and cleared
            // when it ends; it is backed by an AtomicInteger, so polling it from here is race-free.
            // JUnit runs these tests sequentially, so no other run can flip the marker
            // concurrently.
            boolean sawRunActive = false;
            long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(30);
            while (System.nanoTime() < deadline && driver.isAlive()) {
                if (ParallelProver.isMultiThreadedRunActive()) {
                    sawRunActive = true;
                    break;
                }
                Thread.sleep(5);
            }
            assertTrue(sawRunActive,
                "parallel run never became active; the stop test would be vacuous");
            // Let a worker get past scope-entry and into an actual rule step before stopping it the
            // way SwingWorker.cancel(true) does, so the interrupt lands while work is in flight.
            Thread.sleep(100);
            driver.interrupt();

            driver.join(60_000);
            assertFalse(driver.isAlive(),
                "start() did not return within 60s after interrupt (hang)");

            // The invariant: start() must not return until every worker has stopped, otherwise a
            // lingering worker can deliver proof-tree events into the re-attached Swing listeners.
            List<String> live = liveWorkerThreads();
            assertTrue(live.isEmpty(),
                "parallel worker(s) still alive after start() returned: " + live);

            // Non-vacuity backstop: the run committed real work before it was stopped. Safe to read
            // the tree now -- every worker has terminated (asserted above), so countNodes() no
            // longer races a concurrent commitRuleApp.
            assertTrue(proof.countNodes() > 1,
                "the run applied no rule before the interrupt; the stop test is vacuous");
        } finally {
            env.dispose();
            restore(ParallelProver.PARALLEL_PROPERTY, prevEnabled);
            restore(ParallelProver.THREADS_PROPERTY, prevThreads);
        }
    }

    private static List<String> liveWorkerThreads() {
        return Thread.getAllStackTraces().keySet().stream().filter(Thread::isAlive)
                .map(Thread::getName).filter(n -> n.startsWith("key-prover-"))
                .collect(Collectors.toList());
    }

    private static void restore(String key, String previous) {
        if (previous == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, previous);
        }
    }
}
