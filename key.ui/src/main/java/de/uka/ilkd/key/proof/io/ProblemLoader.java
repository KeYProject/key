/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io;

import java.nio.file.Path;
import java.util.List;
import java.util.Properties;
import javax.swing.SwingWorker;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.notification.events.ExceptionFailureEvent;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.prover.impl.DefaultTaskFinishedInfo;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;

import org.key_project.prover.engine.ProverTaskListener;
import org.key_project.prover.engine.TaskFinishedInfo;
import org.key_project.prover.engine.TaskStartedInfo;
import org.key_project.prover.engine.TaskStartedInfo.TaskKind;

/**
 * This class extends the functionality of the {@link AbstractProblemLoader}. It allows to do the
 * loading process as {@link SwingWorker} {@link Thread} and it opens the proof obligation browser
 * it is not possible to instantiate a proof configured by the opened file.
 *
 * @author Martin Hentschel
 */
public final class ProblemLoader extends AbstractProblemLoader { // TODO: Rename in
                                                                 // MultiThreadProblemLoader analog
                                                                 // to SingleThreadProblemLoader
                                                                 // because it uses multiple Threads
                                                                 // (UI and SwingWorker)?

    private final ProverTaskListener ptl;

    private final KeYMediator mediator;

    public ProblemLoader(Path file, List<Path> classPath, Path bootClassPath, List<Path> includes,
            Profile profileOfNewProofs, boolean forceNewProfileOfNewProofs, KeYMediator mediator,
            boolean askUiToSelectAProofObligationIfNotDefinedByLoadedFile,
            Properties poPropertiesToForce, ProverTaskListener ptl) {
        super(file, classPath, bootClassPath, includes, profileOfNewProofs,
            forceNewProfileOfNewProofs, mediator.getUI(),
            askUiToSelectAProofObligationIfNotDefinedByLoadedFile, poPropertiesToForce);
        this.mediator = mediator;
        this.ptl = ptl;
    }

    public void runSynchronously() {
        mediator.stopInterface(true);
        fireTaskStarted();

        final long currentTime = System.currentTimeMillis();
        Throwable message;
        try {
            message = doWork();
        } catch (Throwable ex) {
            message = ex;
        }

        long runTime = System.currentTimeMillis() - currentTime;
        if (message != null) {
            final String errorMessage = "Failed to load "
                + (getEnvInput() == null ? "problem/proof" : getEnvInput().name());
            mediator.notify(new ExceptionFailureEvent(errorMessage, message));
            mediator.getUI().reportStatus(this, errorMessage);
        }
        fireTaskFinished(runTime, message);
    }

    private Throwable doWork() {
        try {
            load(mediator::fireProofLoaded);
            return null;
        } catch (Exception exception) {
            return exception;
        }
    }

    private void fireTaskStarted() {
        if (ptl != null) {
            ptl.taskStarted(new DefaultTaskStartedInfo(TaskKind.Loading, "Loading problem ...", 0));
        }
    }

    private void fireTaskFinished(long runningTime, final Throwable message) {
        if (ptl != null) {
            final TaskFinishedInfo tfi = new DefaultTaskFinishedInfo(ProblemLoader.this, message,
                getProof(), runningTime, (getProof() != null ? getProof().countNodes() : 0),
                (getProof() != null ? getProof().countBranches() - getProof().openGoals().size()
                        : 0));
            ptl.taskFinished(tfi);
        }
    }



    @Override
    protected void selectAndLoadProof(ProblemLoaderControl control, InitConfig initConfig) {
        if (control.selectProofObligation(initConfig)) {
            setProof(mediator.getSelectedProof());
        }
    }

    /**
     * Launch a loading process asynchronously (on a swingworker thread).
     *
     * The start is announced by invoking {@link ProverTaskListener#taskStarted(TaskStartedInfo)} on
     * the
     * registered listener.
     *
     * Termination is announced by invoking
     * {@link ProverTaskListener#taskFinished(TaskFinishedInfo)} on the registered listener.
     */
    public void runAsynchronously() {
        final SwingWorker<Throwable, Void> worker = new SwingWorker<>() {

            private long runTime;

            @Override
            protected Throwable doInBackground() {
                long currentTime = System.currentTimeMillis();
                final Throwable message = doWork();
                runTime = System.currentTimeMillis() - currentTime;
                return message;
            }

            @Override
            protected void done() {
                Throwable message = null;
                try {
                    message = get();
                } catch (final Throwable exception) {
                    // catch exception if something has been thrown in the meantime
                    message = exception;
                } finally {
                    mediator.startInterface(true);
                    if (message != null) {
                        final String errorMessage = "Failed to load "
                            + (getEnvInput() == null ? "problem/proof" : getEnvInput().name());
                        mediator.notify(new ExceptionFailureEvent(errorMessage, message));
                        mediator.getUI().reportStatus(this, errorMessage);
                    }
                    fireTaskFinished(runTime, message);
                    if (mediator.getSelectedProof() != null) {
                        mediator.getSelectionModel().defaultSelection();
                    }
                }
            }
        };

        mediator.stopInterface(true);
        fireTaskStarted();
        worker.execute();
    }
}
