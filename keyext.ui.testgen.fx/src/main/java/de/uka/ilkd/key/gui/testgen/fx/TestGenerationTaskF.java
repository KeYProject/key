/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2,
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.testgen.fx;

import java.util.concurrent.atomic.AtomicReference;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.proof.Proof;

import javafx.concurrent.Task;

import org.jspecify.annotations.NullMarked;

/**
 * Runs the test-case generation off the FX thread, FX port of {@code TGWorker} (Swing
 * TGWorker.java:30-86). The Swing worker is a {@code SwingWorker} that wraps the
 * {@code MainWindowTestGenerator} ({@code AbstractTestGenerator} subclass) and reports through
 * the lifecycle logger of the {@code TGInfoDialog}; this port drives the reflective port of the
 * Swing {@code TestgenFacade} pipeline ({@link TestgenReflectionF#generateTestcases}) in a
 * {@link Task} and dispatches the report events to the {@link LogSinkF} of the
 * {@code TestGenResultsDialogF}.
 * <p>
 * The auto-mode shell is the Swing {@code TGWorker.start/done} parity (TGWorker.java:42-47,
 * :57-62): {@link #call()} performs {@code mediator.initiateAutoMode(proof, true, false)} before
 * the generation (the Swing {@code start()} does it before {@code execute()}) and the
 * terminal-state hooks (the FX-thread counterparts of the Swing {@code done()}) perform
 * {@code mediator.finishAutoMode(proof, true, true, null)} — also after a stop/failure, so the
 * interface never stays frozen. The cooperative stop is the Swing {@code interruptionPerformed}
 * parity (TGWorker.java:66-71): the stop flag is visible to the pipeline between the phases, the
 * {@code SolverLauncher} handle (obtained through {@code launcherRef} — the Swing
 * {@code stopSMTLauncher}) is stopped and the worker thread interrupted as the backup.
 */
@NullMarked
final class TestGenerationTaskF extends Task<Void> {

    /** the UserInterfaceControl of the main window (reflectively obtained). */
    private final Object ui;

    /** the proof to generate test cases for (reflectively obtained). */
    private final Proof proof;

    /** the mediator for the auto-mode shell (Swing TGWorker.start/done). */
    private final KeYMediatorF mediator;

    /** the log sink of the run dialog (events fire on this worker thread). */
    private final LogSinkF sink;

    /** the running {@code SolverLauncher} (the Swing {@code stopSMTLauncher} handle). */
    private final AtomicReference<Object> launcher = new AtomicReference<>();

    private volatile boolean stopRequested;

    TestGenerationTaskF(KeYMediatorF mediator, Object ui, Proof proof, LogSinkF sink) {
        // mediator/ui/proof mirror TGWorker's getMediator(), "the selected proof" and the main
        // window's UI (TGWorker.java:36-40).
        this.mediator = mediator;
        this.ui = ui;
        this.proof = proof;
        this.sink = sink;
    }

    @Override
    protected Void call() throws Exception {
        // Swing TGWorker.start(): initiateAutoMode before the run (there on the EDT, here at the
        // beginning of the worker body — the FX mediator's seam only flips flags and publishes
        // the observable property, which the listeners marshal to the FX thread).
        mediator.initiateAutoMode(proof, true, false);
        TestgenReflectionF.generateTestcases(ui, proof, this::isStopRequested, sink, launcher);
        return null;
    }

    boolean isStopRequested() {
        return stopRequested;
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
     * Swing TGWorker.done(): {@code finishAutoMode(originalProof, true, true, null)} — runs on
     * the FX thread (the state-change hooks), also after a stop or failure.
     */
    private void finishAutoMode() {
        mediator.finishAutoMode(proof, true, true, null);
    }

    /**
     * Asks the running generation to stop (Swing TGWorker.interruptionPerformed,
     * TGWorker.java:66-71): the flag is visible to the pipeline between the phases, the
     * {@code SolverLauncher} is stopped ({@code stopSMTLauncher}) and the worker thread
     * interrupted as the backup (the macros honour the interrupt).
     */
    void requestStop() {
        stopRequested = true;
        Object running = launcher.get();
        if (running != null) {
            TestgenReflectionF.stopLauncher(running);
        }
        if (isRunning()) {
            cancel(true);
        }
    }
}
