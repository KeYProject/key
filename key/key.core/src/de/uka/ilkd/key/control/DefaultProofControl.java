package de.uka.ilkd.key.control;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.util.ProofStarter;

/**
 * The default implementation of {@link ProofControl}.
 * @author Martin Hentschel
 */
public class DefaultProofControl extends AbstractProofControl {
   /**
    * The currently running {@link AutoModeThread}.
    */
   private AutoModeThread autoModeThread;

   /**
    * Constructor.
    * @param defaultProverTaskListener The default {@link ProverTaskListener} which will be added to all started {@link ApplyStrategy} instances.
    */
   public DefaultProofControl(ProverTaskListener defaultProverTaskListener) {
      super(defaultProverTaskListener);
   }

   /**
    * Constructor.
    * @param defaultProverTaskListener The default {@link ProverTaskListener} which will be added to all started {@link ApplyStrategy} instances.
    * @param ruleCompletionHandler An optional {@link RuleCompletionHandler}.
    */
   public DefaultProofControl(ProverTaskListener defaultProverTaskListener,
                              RuleCompletionHandler ruleCompletionHandler) {
      super(defaultProverTaskListener, ruleCompletionHandler);
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
}
