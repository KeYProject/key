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
import de.uka.ilkd.key.util.ExceptionHandlerException;
import de.uka.ilkd.key.util.KeYExceptionHandler;

/**
 * This class extends the functionality of the {@link DefaultProblemLoader}.
 * It allows to do the loading process as {@link SwingWorker} {@link Thread}
 * and it opens the proof obligation browser it is not possible to instantiate
 * a proof configured by the opened file.
 * @author Martin Hentschel
 */
public final class ProblemLoader extends DefaultProblemLoader implements Runnable {
   private SwingWorker worker;
   private ProverTaskListener ptl;

   public ProblemLoader(File file, List<File> classPath, File bootClassPath, KeYMediator mediator) {
      super(file, classPath, bootClassPath, mediator);
   }

   public void addTaskListener(ProverTaskListener ptl) {
      this.ptl = ptl;
   }    

   public void run() {
      /*
       * Invoking start() on the SwingWorker causes a new Thread to be created
       * that will call construct(), and then finished(). Note that finished()
       * is called even if the worker is interrupted because we catch the
       * InterruptedException in doWork().
       */
      worker = new SwingWorker() {
         private long time;

         @Override
         public Object construct() {
            time = System.currentTimeMillis();
            String res = doWork();
            time = System.currentTimeMillis() - time;
            return res;
         }

         @Override
         public void finished() {
            getMediator().startInterface(true);
            final String msg = (String) get();
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
      worker.start();
   }
    
   private String doWork() {
      String status = "";
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
            status = thr.getMessage();
            System.err.println("2");
         }
      }
      catch (ExceptionHandlerException ex) {
         String errorMessage = "Failed to load " + (getEnvInput() == null ? "problem/proof" : getEnvInput().name());
         getMediator().getUI().notify(new ExceptionFailureEvent(errorMessage, ex));
         getMediator().getUI().reportStatus(this, errorMessage);
         status = ex.toString();
      }
      return status;
   }

   public KeYExceptionHandler getExceptionHandler() {
       return getMediator().getExceptionHandler();
   }
   
   @Override
   protected String selectProofObligation() {
      ProofManagementDialog.showInstance(getMediator(), getInitConfig());
      if (ProofManagementDialog.startedProof()) {
         return "";
      }
      else {
         return "Aborted.";
      }
   }
}
