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
import javax.swing.SwingWorker;

/**
 * This class extends the functionality of the {@link DefaultProblemLoader}. It
 * allows to do the loading process as {@link SwingWorker3} {@link Thread} and
 * it opens the proof obligation browser it is not possible to instantiate a
 * proof configured by the opened file.
 *
 * @author Martin Hentschel
 */
public final class ProblemLoader extends DefaultProblemLoader implements Runnable {

    private SwingWorker worker;
    private ProverTaskListener ptl;

    public ProblemLoader(File file, List<File> classPath, File bootClassPath, Profile profileOfNewProofs, KeYMediator mediator) {
        super(file, classPath, bootClassPath, profileOfNewProofs, mediator);
    }

    public void addTaskListener(ProverTaskListener ptl) {
        this.ptl = ptl;
    }

    @Override
    public void run() {
        /*
         * Invoking execute() on the SwingWorker causes a new Thread to be
         * created that will call construct(), and then finished(). Note
         * that done() is called even if the worker is interrupted
         * because we catch the InterruptedException in doWork().
         */
        worker = new SwingWorker<Object, Object>() {

            private long time;

            @Override
            protected Object doInBackground() throws Exception {
                time = System.currentTimeMillis();
                Object res = doWork();
                time = System.currentTimeMillis() - time;
                return res;
            }

            @Override
            protected void done() {
                getMediator().startInterface(true);
                Object msg;
                try {
                    msg = get();
                } catch (Exception exception) {
                    getExceptionHandler().reportException(exception);
                    msg = null;
                }

                if (ptl != null) {
                    final TaskFinishedInfo tfi = new DefaultTaskFinishedInfo(ProblemLoader.this, msg, getProof(), time, (getProof() != null ? getProof().countNodes() : 0), (getProof() != null ? getProof().countBranches() - getProof().openGoals().size() : 0));
                    ptl.taskFinished(tfi);
                }
            }

        };

        getMediator().stopInterface(true);
        if (ptl != null) {
            ptl.taskStarted("Loading problem ...", 0);
        }
        worker.execute();
    }

    private Throwable doWork() {
        Throwable status = null;
        try {
            try {
                status = load();
            } catch (ExceptionHandlerException e) {
                // e.printStackTrace();
                throw e;
            } catch (Throwable thr) {
                getExceptionHandler().reportException(thr);
                status = thr;
            }
        } catch (ExceptionHandlerException ex) {
            String errorMessage = "Failed to load " + (getEnvInput() == null ? "problem/proof" : getEnvInput().name());
            getMediator().getUI().notify(new ExceptionFailureEvent(errorMessage, ex));
            getMediator().getUI().reportStatus(this, errorMessage);
            status = ex;
        }
        return status;
    }

    public KeYExceptionHandler getExceptionHandler() {
        return getMediator().getExceptionHandler();
    }

    @Override
    protected ProblemLoaderException selectProofObligation() {
        ProofManagementDialog.showInstance(getInitConfig());
        if (ProofManagementDialog.startedProof()) {
            return null;
        } else {
            return new ProblemLoaderException(this, "Aborted.");
        }
    }
}
