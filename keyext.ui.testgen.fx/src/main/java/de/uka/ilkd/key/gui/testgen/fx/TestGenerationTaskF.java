/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.testgen.fx;

import javafx.concurrent.Task;

import org.jspecify.annotations.NullMarked;

/**
 * Runs the test-case generation off the FX thread, FX port of {@code TGWorker} (Swing
 * TGWorker.java:30-86). The Swing worker is a {@code SwingWorker} that wraps the
 * {@code MainWindowTestGenerator} ({@code AbstractTestGenerator} subclass) and reports through
 * the lifecycle logger of the {@code TGInfoDialog}; this port wraps the headless CLI pipeline
 * ({@link TestgenReflectionF#generateTestcases}) in a {@link Task} and dispatches the report
 * events to the {@link LogSinkF} of the {@code TestGenResultsDialogF}.
 * <p>
 * <b>KNOWN-SIMPLIFIED:</b> the Swing worker additionally puts the original proof into the
 * mediator's auto-mode machinery ({@code initiateAutoMode}/{@code finishAutoMode},
 * TGWorker.java:42-63) and stops cooperatively through the {@code StopRequest} flag and the
 * generator's {@code stopSMTLauncher} (TGWorker.java:66-71); the facade route has no launcher
 * handle, so {@link #requestStop()} interrupts the worker thread, which the generation macros
 * honour between phases (the final Z3 CE launch itself runs until it returns).
 */
@NullMarked
final class TestGenerationTaskF extends Task<Void> {

    /** the UserInterfaceControl of the main window (reflectively obtained). */
    private final Object ui;

    /** the proof to generate test cases for (reflectively obtained). */
    private final Object proof;

    /** the log sink of the run dialog (events fire on this worker thread). */
    private final LogSinkF sink;

    private volatile boolean stopRequested;

    TestGenerationTaskF(Object ui, Object proof, LogSinkF sink) {
        // ui/proof mirror TGWorker's "the selected proof" and the main window's UI
        // (TGWorker.java:36-39).
        this.ui = ui;
        this.proof = proof;
        this.sink = sink;
    }

    @Override
    protected Void call() throws Exception {
        TestgenReflectionF.generateTestcases(ui, proof, sink);
        return null;
    }

    boolean isStopRequested() {
        return stopRequested;
    }

    /**
     * Asks the running generation to stop: the flag is visible to the dialogs, the interrupt is
     * honoured by the generation macros (see the class comment).
     */
    void requestStop() {
        stopRequested = true;
        if (isRunning()) {
            cancel(true);
        }
    }
}
