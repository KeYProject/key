// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//


package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.util.List;

import de.uka.ilkd.key.gui.DefaultTaskFinishedInfo;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProofManagementDialog;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.SwingWorker;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.gui.notification.events.ExceptionFailureEvent;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.util.ExceptionHandlerException;
import de.uka.ilkd.key.util.KeYExceptionHandler;

/**
 * This class extends the functionality of the {@link DefaultProblemLoader}.
 * It allows to do the loading process as {@link SwingWorker} {@link Thread}
 * and it opens the proof obligation browser it is not possible to instantiate
 * a proof configured by the opened file.
 * @author Martin Hentschel
 */
public class ProblemLoader extends DefaultProblemLoader {

   private ProverTaskListener ptl;

   public ProblemLoader(File file, List<File> classPath, File bootClassPath, Profile profileOfNewProofs, KeYMediator mediator) {
      super(file, classPath, bootClassPath, profileOfNewProofs, mediator);
   }

   public void addTaskListener(ProverTaskListener ptl) {
      this.ptl = ptl;
   }

    public void run() {

        getMediator().stopInterface(true);
        if (ptl != null) {
            ptl.taskStarted("Loading problem ...", 0);
        }

        long time;

        System.out.println("Loading: " + file);
        time = System.currentTimeMillis();
        final Object msg = doWork();
        time = System.currentTimeMillis() - time;

        getMediator().startInterface(true);
        if (ptl != null) {
            final TaskFinishedInfo tfi = new DefaultTaskFinishedInfo(ProblemLoader.this, msg, getProof(), time, (getProof() != null ? getProof().countNodes() : 0), (getProof() != null ? getProof().countBranches() - getProof().openGoals().size() : 0));
            ptl.taskFinished(tfi);
        }
    }

   private Throwable doWork() {
      Throwable status = null;
      try {
         try {
            status = load(true);
         }
         catch (ExceptionHandlerException e) {
            // e.printStackTrace();
            throw e;
         }
         catch (Throwable thr) {
            getExceptionHandler().reportException(thr);
            status = thr;
         }
      }
      catch (ExceptionHandlerException ex) {
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
      }
      else {
         return new ProblemLoaderException(this, "Aborted.");
      }
   }
}
