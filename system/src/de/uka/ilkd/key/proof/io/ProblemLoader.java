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

import java.io.File;
import java.util.List;

import de.uka.ilkd.key.core.DefaultTaskFinishedInfo;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.ProverTaskListener;
import de.uka.ilkd.key.core.TaskFinishedInfo;
import de.uka.ilkd.key.gui.notification.events.ExceptionFailureEvent;
import de.uka.ilkd.key.proof.init.Profile;
import java.util.Properties;

import javax.swing.SwingWorker;

/**
 * This class extends the functionality of the {@link AbstractProblemLoader}. It
 * allows to do the loading process as {@link SwingWorker3} {@link Thread} and
 * it opens the proof obligation browser it is not possible to instantiate a
 * proof configured by the opened file.
 *
 * @author Martin Hentschel
 */
public final class ProblemLoader extends AbstractProblemLoader { // TODO: Rename in MultiThreadProblemLoader analog to SingleThreadProblemLoader because it uses multiple Threads (UI and SwingWorker)?

   private final ProverTaskListener ptl;

   public ProblemLoader(File file, List<File> classPath, File bootClassPath,
                        Profile profileOfNewProofs, KeYMediator mediator,
                        boolean askUiToSelectAProofObligationIfNotDefinedByLoadedFile,
                        Properties poPropertiesToForce, ProverTaskListener ptl) {
      super(file, classPath, bootClassPath, profileOfNewProofs, mediator,
            askUiToSelectAProofObligationIfNotDefinedByLoadedFile, poPropertiesToForce);
      this.ptl = ptl;
   }

   public void runSynchronously() {
       getMediator().stopInterface(true);
       fireTaskStarted();

       final long currentTime = System.currentTimeMillis();
       Throwable message;
       try {
           message = doWork();
       } catch(Throwable ex) {
           message = ex;
       }

       long runTime = System.currentTimeMillis() - currentTime;
       fireTaskFinished(runTime, message);
   }

   private Throwable doWork() {
      try {
          load();
          return null;
      } catch (Throwable exception) {
          final String errorMessage = "Failed to load "
                  + (getEnvInput() == null ? "problem/proof" : getEnvInput().name());
          getMediator().getUI().notify(new ExceptionFailureEvent(errorMessage, exception));
          getMediator().getUI().reportStatus(this, errorMessage);
          return exception;
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

    /**
     * Launch a loading process asynchronously (on a swingworker thread).
     *
     * The start is announced by invoking
     * {@link ProverTaskListener#taskStarted(String, int)} on the registered
     * listener.
     *
     * Termination is announced by invoking
     * {@link ProverTaskListener#taskFinished(TaskFinishedInfo)} on the
     * registered listener.
     */
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
               } catch (final Throwable exception) {
                   // catch exception if something has been thrown in the meantime
                   message = exception;
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