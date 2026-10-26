/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
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

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This class extends the functionality of the {@link AbstractProblemLoader}. It allows to do the
 * loading process as {@link SwingWorker} {@link Thread} and it opens the proof obligation browser
 * it is not possible to instantiate a proof configured by the opened file.
 *
 * @author Martin Hentschel
 */
@NullMarked
public final class ProblemLoader extends AbstractProblemLoader {
    // TODO: Rename in MultiThreadProblemLoader analog to SingleThreadProblemLoader because it uses
    // multiple Threads
    // (UI and SwingWorker)?

    private final @Nullable ProverTaskListener ptl;

    private final KeYMediator mediator;

    /**
     * The legacy {@link AbstractProblemLoader} declares its {@code poPropertiesToForce} parameter
     * {@code @NonNull}, but forcing problem options is optional and the existing callers pass a
     * possibly-{@code null} value, which the loader tolerates (it only consults the properties
     * when forcing is requested), suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    public ProblemLoader(Path file, @Nullable List<Path> classPath, @Nullable Path bootClassPath,
            @Nullable List<Path> includes, Profile profileOfNewProofs,
            boolean forceNewProfileOfNewProofs, KeYMediator mediator,
            boolean askUiToSelectAProofObligationIfNotDefinedByLoadedFile,
            @Nullable Properties poPropertiesToForce, @Nullable ProverTaskListener ptl) {
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
            var envInput = getEnvInput();
            final String errorMessage = "Failed to load "
                + (envInput == null ? "problem/proof" : envInput.name());
            mediator.notify(new ExceptionFailureEvent(errorMessage, message));
            mediator.getUI().reportStatus(this, errorMessage);
        }
        fireTaskFinished(runTime, message);
    }

    private @Nullable Throwable doWork() {
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

    private void fireTaskFinished(long runningTime, final @Nullable Throwable message) {
        if (ptl != null) {
            // {@code getProof()} returns a possibly-null value whose nullness refinement does not
            // survive repeated calls; work on a local copy
            var proof = getProof();
            final TaskFinishedInfo tfi = new DefaultTaskFinishedInfo(ProblemLoader.this, message,
                proof, runningTime, (proof != null ? proof.countNodes() : 0),
                (proof != null ? proof.countBranches() - proof.openGoals().size() : 0));
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
        final SwingWorker<@Nullable Throwable, Void> worker =
            new SwingWorker<@Nullable Throwable, Void>() {

            private long runTime;

            @Override
            protected @Nullable Throwable doInBackground() {
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
