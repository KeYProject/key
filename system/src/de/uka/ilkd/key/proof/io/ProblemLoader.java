// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.proof.io;

import de.uka.ilkd.key.gui.*;
import de.uka.ilkd.key.gui.notification.events.ExceptionFailureEvent;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.util.ExceptionHandlerException;
import de.uka.ilkd.key.util.KeYExceptionHandler;
import java.io.File;
import java.util.List;
import java.util.Properties;

import javax.swing.SwingWorker;

/**
 * This class extends the functionality of the {@link DefaultProblemLoader}. It
 * allows to do the loading process as {@link SwingWorker3} {@link Thread} and
 * it opens the proof obligation browser it is not possible to instantiate a
 * proof configured by the opened file.
 *
 * @author Martin Hentschel
 */
public final class ProblemLoader extends DefaultProblemLoader {

    private ProverTaskListener ptl;

    public ProblemLoader(File file, List<File> classPath, File bootClassPath,
                         Profile profileOfNewProofs, KeYMediator mediator,
                         boolean askUiToSelectAProofObligationIfNotDefinedByLoadedFile,
                         Properties poPropertiesToForce) {
        super(file, classPath, bootClassPath, profileOfNewProofs, mediator,
              askUiToSelectAProofObligationIfNotDefinedByLoadedFile, poPropertiesToForce);
    }

    public void addTaskListener(final ProverTaskListener ptl) {
        this.ptl = ptl;
    }

    public void runSynchronously() {
        getMediator().stopInterface(true);
        fireTaskStarted();

        final long currentTime = System.currentTimeMillis();
        final Throwable message = doWork();
        long runTime = System.currentTimeMillis() - currentTime;

        fireTaskFinished(runTime, message);
        reportException(message);
    }

    private Throwable doWork() {
        try {
            return load();
        } catch (final ExceptionHandlerException exception) {
            final String errorMessage = "Failed to load "
                    + (getEnvInput() == null ? "problem/proof" : getEnvInput().name());
            getMediator().getUI().notify(new ExceptionFailureEvent(errorMessage, exception));
            getMediator().getUI().reportStatus(this, errorMessage);
            return exception;
        } catch (final Throwable throwable) {
        	throwable.printStackTrace();
            reportException(throwable);
            return throwable;
        }
    }

    private void fireTaskStarted() {
        if (ptl != null) {
            ptl.taskStarted("Loading problem ...", 0);
        }
    }

    private void fireTaskFinished(long runningTime, final Throwable message) {
        if (ptl != null) {
            final TaskFinishedInfo tfi = new DefaultTaskFinishedInfo(ProblemLoader.this, message,
                    getProof(), runningTime, (getProof() != null ? getProof().countNodes() : 0),
                    (getProof() != null ? getProof().countBranches() - getProof().openGoals().size() : 0));
            ptl.taskFinished(tfi);
        }
    }

    private void reportException(final Throwable message) {
        if (message != null) {
            getExceptionHandler().reportException(message);
        }
    }

    public KeYExceptionHandler getExceptionHandler() {
        return getMediator().getExceptionHandler();
    }

    public void runAsynchronously() {
        final SwingWorker<Throwable, Void> worker =
                new SwingWorker<Throwable, Void>() {

            private long runTime;

            @Override
            protected Throwable doInBackground() throws Exception {
                long currentTime = System.currentTimeMillis();
                final Throwable message = doWork();
                runTime = System.currentTimeMillis() - currentTime;
                return message;
            }

            @Override
            protected void done() {
                getMediator().startInterface(true);
                Throwable message = null;
                try {
                    message = get();                    
                } catch (final Exception exception) {
                    message = exception;
                    getExceptionHandler().reportException(exception.getCause() != null ? 
                            exception.getCause() : exception);
                } finally {
                    fireTaskFinished(runTime, message);
                }
            }
        };

        getMediator().stopInterface(true);
        fireTaskStarted();
        worker.execute();
    }

}