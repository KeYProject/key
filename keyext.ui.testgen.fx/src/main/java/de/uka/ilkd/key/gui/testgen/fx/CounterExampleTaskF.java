/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.testgen.fx;

import java.util.concurrent.atomic.AtomicReference;
import javafx.concurrent.Task;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.proof.Proof;

import org.jspecify.annotations.NullMarked;

/**
 * Runs the counterexample search off the FX thread, FX port of the Swing
 * {@code CounterExampleAction.CEWorker} (CounterExampleAction.java:160-194). The Swing worker
 * runs {@code AbstractSideProofCounterExampleGenerator.searchCounterExample} in a
 * {@code SwingWorker} and reports through the {@code SolverListener} (with progress/result
 * dialogs); this port runs the reflective counterpart of the same search
 * ({@link TestgenReflectionF#searchCounterExample}) in a {@link Task} and streams the SMT
 * statistics into the {@link LogSinkF} of the {@code CounterExampleResultsDialogF}.
 * <p>
 * The auto-mode shell is the Swing {@code CEWorker.start/done} parity
 * (CounterExampleAction.java:169-191): {@link #call()} performs
 * {@code mediator.initiateAutoMode(proof, true, false)} before the search and the terminal-state
 * hooks (the FX-thread counterparts of the Swing {@code done()}) perform
 * {@code mediator.finishAutoMode(proof, true, true, null)} — also after a stop/failure, so the
 * interface never stays frozen.
 * <p>
 * <b>KNOWN-SIMPLIFIED:</b> the Swing {@code SolverListener} opens a modal progress dialog and a
 * results dialog showing the counterexample model (SolverListener.java); the FX port prints the
 * SMT statistics and the found/not-found outcome into the run dialog's log and leaves the model
 * inspection to the generated test data / subsequent runs (the C4 {@code SolverListenerF} route
 * brings the dialogs back).
 */
@NullMarked
final class CounterExampleTaskF extends Task<Void> {

    /** the UserInterfaceControl of the main window (reflectively obtained). */
    private final Object ui;

    /** the proof of the selected goal (reflectively obtained). */
    private final Proof proof;

    /** the sequent of the selected goal (reflectively obtained). */
    private final Object sequent;

    /** the mediator for the auto-mode shell (Swing CEWorker.start/done). */
    private final KeYMediatorF mediator;

    /** the log sink of the run dialog (events fire on this worker thread). */
    private final LogSinkF sink;

    /** the running {@code SolverLauncher} (reflectively obtained), for the Stop button. */
    private final AtomicReference<Object> launcher = new AtomicReference<>();

    CounterExampleTaskF(KeYMediatorF mediator, Object ui, Proof proof, Object sequent,
            LogSinkF sink) {
        // mediator/ui/proof/sequent mirror the Swing worker's inputs (CounterExampleAction
        // .start, CounterExampleAction.java:169-172: the proof of the selected goal).
        this.mediator = mediator;
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
        TestgenReflectionF.searchCounterExample(ui, proof, sequent, sink, launcher);
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
