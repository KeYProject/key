/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.testgen.fx;

import java.util.concurrent.atomic.AtomicReference;
import javafx.concurrent.Task;
import javafx.stage.Stage;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.smt.SolverListenerF;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.DefaultSMTSettings;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Runs the counterexample search off the FX thread, FX port of the Swing
 * {@code CounterExampleAction.CEWorker} (CounterExampleAction.java:160-194). The Swing worker
 * runs {@code AbstractSideProofCounterExampleGenerator.searchCounterExample} in a
 * {@code SwingWorker} with the {@code createSolverListener} hook answering
 * {@code new SolverListener(settings, proof)} (CounterExampleAction.java:186-188); this port runs
 * the reflective counterpart of the same search ({@link TestgenReflectionF#searchCounterExample})
 * in a {@link Task} with the same hook answering a {@link SolverListenerF} (the modal progress
 * dialog and the results/counterexample-model dialogs, WP-7) and streams the pipeline messages
 * into the {@link LogSinkF} of the {@code CounterExampleResultsDialogF}.
 * <p>
 * The auto-mode shell is the Swing {@code CEWorker.start/done} parity
 * (CounterExampleAction.java:169-191): {@link #call()} performs
 * {@code mediator.initiateAutoMode(proof, true, false)} before the search and the terminal-state
 * hooks (the FX-thread counterparts of the Swing {@code done()}) perform
 * {@code mediator.finishAutoMode(proof, true, true, null)} — also after a stop/failure, so the
 * interface never stays frozen.
 */
@NullMarked
final class CounterExampleTaskF extends Task<Void> {

    /** the UserInterfaceControl of the main window (reflectively obtained). */
    private final Object ui;

    /** the proof of the selected goal (reflectively obtained). */
    private final Proof proof;

    /** the sequent of the selected goal (reflectively obtained). */
    private final Object sequent;

    /** the mediator for the auto-mode shell (Swing CEWorker.start/done) and the listener. */
    private final KeYMediatorF mediator;

    /** the owner window of the {@code SolverListenerF} progress dialog (may be {@code null}). */
    private final @Nullable Stage owner;

    /** the log sink of the run dialog (events fire on this worker thread). */
    private final LogSinkF sink;

    /** the running {@code SolverLauncher} (reflectively obtained), for the Stop button. */
    private final AtomicReference<Object> launcher = new AtomicReference<>();

    CounterExampleTaskF(KeYMediatorF mediator, @Nullable Stage owner, Object ui, Proof proof,
            Object sequent, LogSinkF sink) {
        // mediator/ui/proof/sequent mirror the Swing worker's inputs (CounterExampleAction
        // .start, CounterExampleAction.java:169-172: the proof of the selected goal); the owner
        // is the Swing SolverListener's dialog owner.
        this.mediator = mediator;
        this.owner = owner;
        this.ui = ui;
        this.proof = proof;
        this.sequent = sequent;
        this.sink = sink;
    }

    @Override
    protected Void call() throws Exception {
        // Swing CEWorker.start(): initiateAutoMode before the search (CounterExampleAction
        // .java:169-172; there on the EDT, here at the beginning of the worker body — the FX
        // mediator's seam only flips flags and publishes the observable property).
        mediator.initiateAutoMode(proof, true, false);
        TestgenReflectionF.searchCounterExample(ui, proof, sequent, sink, launcher,
            // Swing CEWorker.createSolverListener (CounterExampleAction.java:186-188): the
            // SolverListener for the settings + side proof of the search
            (settings, sideProof) -> new SolverListenerF((DefaultSMTSettings) settings,
                (Proof) sideProof, owner, mediator));
        return null;
    }

    @Override
    protected void succeeded() {
        finishAutoMode();
    }

    @Override
    protected void failed() {
        finishAutoMode();
    }

    @Override
    protected void cancelled() {
        finishAutoMode();
    }

    /**
     * Swing CEWorker.done(): {@code finishAutoMode(oldProof, true, true, null)}
     * (CounterExampleAction.java:174-176) — runs on the FX thread (the state-change hooks), also
     * after a stop or failure.
     */
    private void finishAutoMode() {
        mediator.finishAutoMode(proof, true, true, null);
    }

    /**
     * Asks the running search to stop: the reflective {@code SolverLauncher} is stopped and the
     * worker thread interrupted (the {@code SemanticsBlastingMacro} honours the interrupt).
     */
    void requestStop() {
        Object running = launcher.get();
        if (running != null) {
            TestgenReflectionF.stopLauncher(running);
        }
        if (isRunning()) {
            cancel(true);
        }
    }
}
