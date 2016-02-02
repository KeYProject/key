package de.uka.ilkd.key.control;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.DefaultTaskStartedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.TaskFinishedInfo;
import de.uka.ilkd.key.proof.TaskStartedInfo.TaskKind;
import de.uka.ilkd.key.util.ProofStarter;

/**
 * The default implementation of {@link ProofControl}.
 * @author Martin Hentschel
 */
public class DefaultProofControl extends AbstractProofControl {
   /**
    * The {@link UserInterfaceControl} in which this {@link ProofControl} is used.
    */
   private final UserInterfaceControl ui;
   
   /**
    * The currently running {@link Thread}.
    */
   private Thread autoModeThread;

   /**
    * Constructor.
    * @param ui The {@link UserInterfaceControl} in which this {@link ProofControl} is used.
    * @param defaultProverTaskListener The default {@link ProverTaskListener} which will be added to all started {@link ApplyStrategy} instances.
    */
   public DefaultProofControl(UserInterfaceControl ui, DefaultUserInterfaceControl defaultProverTaskListener) {
      super(defaultProverTaskListener);
      this.ui = ui;
   }

   /**
    * Constructor.
    * @param ui The {@link UserInterfaceControl} in which this {@link ProofControl} is used.
    * @param defaultProverTaskListener The default {@link ProverTaskListener} which will be added to all started {@link ApplyStrategy} instances.
    * @param ruleCompletionHandler An optional {@link RuleCompletionHandler}.
    */
   public DefaultProofControl(UserInterfaceControl ui,
                              DefaultUserInterfaceControl defaultProverTaskListener,
                              RuleCompletionHandler ruleCompletionHandler) {
      super(defaultProverTaskListener, ruleCompletionHandler);
      this.ui = ui;
   }

   @Override
   public synchronized void startAutoMode(Proof proof, ImmutableList<Goal> goals, ProverTaskListener ptl) {
      if (!isInAutoMode()) {
         autoModeThread = new AutoModeThread(proof, goals, ptl);
         autoModeThread.start();
      }
   }

   @Override
   public synchronized void stopAutoMode() {
      if (isInAutoMode()) {
         autoModeThread.interrupt();
      }
   }

   @Override
   public void waitWhileAutoMode() {
      while (isInAutoMode()) { // Wait until auto mode has stopped.
         try {
            Thread.sleep(100);
         }
         catch (InterruptedException e) {
         }
      }
   }
   
   @Override
   public boolean isInAutoMode() {
      return autoModeThread != null;
   }

   private class AutoModeThread extends Thread {
      private final Proof proof;
      
      private final ImmutableList<Goal> goals;
      
      private final ProverTaskListener ptl;

      public AutoModeThread(Proof proof, ImmutableList<Goal> goals, ProverTaskListener ptl) {
         this.proof = proof;
         this.goals = goals;
         this.ptl = ptl;
      }

      @Override
      public void run() {
         try {
            fireAutoModeStarted(new ProofEvent(proof));
            ProofStarter starter = ptl != null ?
                                   new ProofStarter(new CompositePTListener(getDefaultProverTaskListener(), ptl), false) :
                                   new ProofStarter(getDefaultProverTaskListener(), false);
            starter.init(proof);
            if (goals != null) {
               starter.start(goals);
            }
            else {
               starter.start();
            }
         }
         finally {
            autoModeThread = null;
            fireAutoModeStopped(new ProofEvent(proof));
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void runMacro(Node node, ProofMacro macro, PosInOccurrence posInOcc) {
      if (!isInAutoMode()) {
         autoModeThread = new MacroThread(node, macro, posInOcc);
         autoModeThread.start();
      }
   }
   
   private class MacroThread extends Thread {
      private final Node node;
      
      private final ProofMacro macro; 
      
      private final PosInOccurrence posInOcc;

      public MacroThread(Node node, ProofMacro macro, PosInOccurrence posInOcc) {
         this.node = node;
         this.macro = macro;
         this.posInOcc = posInOcc;
      }

      @Override
      public void run() {
         Proof proof = node.proof();
         ProverTaskListener ptl = getDefaultProverTaskListener();
         TaskFinishedInfo info = null;
         try {
            fireAutoModeStarted(new ProofEvent(proof));
            info = ProofMacroFinishedInfo.getDefaultInfo(macro, proof);
            if (ptl != null) {
               ptl.taskStarted(new DefaultTaskStartedInfo(TaskKind.Macro, macro.getName(), 0));
            }
            synchronized(macro) {
               info = macro.applyTo(ui, node, posInOcc, ptl);
           }
         }
         catch (Exception e) {
            throw new RuntimeException("Macro caused an exception: " + e.getMessage(), e);
         }
         finally {
            if (ptl != null) {
               ptl.taskFinished(info);
            }
            autoModeThread = null;
            fireAutoModeStopped(new ProofEvent(proof));
         }
      }
   }
}
