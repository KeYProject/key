/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.testgen.fx;

import java.util.concurrent.atomic.AtomicReference;
import javafx.concurrent.Task;

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
 * <b>KNOWN-SIMPLIFIED:</b> the Swing {@code SolverListener} opens a modal progress dialog and a
 * results dialog showing the counterexample model (SolverListener.java); the FX port prints the
 * SMT statistics and the found/not-found outcome into the run dialog's log and leaves the model
 * inspection to the generated test data / subsequent runs. The auto-mode shell of the Swing
 * worker ({@code initiateAutoMode}/{@code finishAutoMode}, CounterExampleAction.java:169-191)
 * is dropped like in {@link TestGenerationTaskF}.
 */
@NullMarked
final class CounterExampleTaskF extends Task<Void> {

    /** the UserInterfaceControl of the main window (reflectively obtained). */
    private final Object ui;

    /** the proof of the selected goal (reflectively obtained). */
    private final Object proof;

    /** the sequent of the selected goal (reflectively obtained). */
    private final Object sequent;

    /** the log sink of the run dialog (events fire on this worker thread). */
    private final LogSinkF sink;

    /** the running {@code SolverLauncher} (reflectively obtained), for the Stop button. */
    private final AtomicReference<Object> launcher = new AtomicReference<>();

    CounterExampleTaskF(Object ui, Object proof, Object sequent, LogSinkF sink) {
        // ui/proof/sequent mirror the Swing worker's inputs (CounterExampleAction.actionPerformed,
        // CounterExampleAction.java:106-120: node.proof() + node.sequent() of the selected goal).
        this.ui = ui;
        this.proof = proof;
        this.sequent = sequent;
        this.sink = sink;
    }

    @Override
    protected Void call() throws Exception {
        TestgenReflectionF.searchCounterExample(ui, proof, sequent, sink, launcher);
        return null;
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
