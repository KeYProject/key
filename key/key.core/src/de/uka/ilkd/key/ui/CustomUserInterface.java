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

package de.uka.ilkd.key.ui;

import java.util.LinkedList;
import java.util.List;

import org.key_project.utils.collection.ImmutableList;

import de.uka.ilkd.key.gui.ApplyTacletDialogModel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.TaskFinishedInfo;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentEvent;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.util.ProofStarter;

/**
 * <p>
 * An extended version of {@link AbstractConsoleUserInterface} which can be used
 * to prove manually instantiated proofs.
 * </p>
 * <p>
 * The basic usage is like:
 * <code><pre>
 * // Create user interface
 * CustomUserInterface ui = new CustomUserInterface(false);
 * // Load java file
 * InitConfig initConfig = ui.load(javaFile, null, null);
 * // Find operation contract to proof in services
 * Services services = initConfig.getServices();
 * FunctionalOperationContract contract ...
 * // Start proof
 * ProofOblInput input = new FunctionalOperationContractPO(initConfig, contract);
 * Proof proof = ui.createProof(initConfig, input);
 * // Run proof in auto mode
 * ui.startAndWaitForProof(proof);
 * </pre></code>
 * </p>
 * @author Martin Hentschel
 */
public class CustomUserInterface extends AbstractUserInterface {
   /**
    * An optional {@link IUserInterfaceCustomization}.
    */
   private final IUserInterfaceCustomization customiaztion;

   /**
    * The currently running {@link AutoModeThread}.
    */
   private AutoModeThread autoModeThread;
   
   /**
    * Contains all available {@link AutoModeListener}.
    */
   private final List<AutoModeListener> autoModeListener = new LinkedList<AutoModeListener>();
   
   /**
    * Constructor.
    */
   public CustomUserInterface() {
      this(null);
   }
   
   /**
    * Constructor.
    * @param customiaztion An optional {@link IUserInterfaceCustomization}.
    */
   public CustomUserInterface(IUserInterfaceCustomization customiaztion) {
      this.customiaztion = customiaztion;
   }
   
   /**
    * {@inheritDoc}
    */   
   @Override
   public void completeAndApplyTacletMatch(ApplyTacletDialogModel[] models, Goal goal) {
      if (customiaztion != null) {
         customiaztion.completeAndApplyTacletMatch(models, goal);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IBuiltInRuleApp completeBuiltInRuleApp(IBuiltInRuleApp app, Goal goal, boolean forced) {
      if (customiaztion == null) {
         return super.completeBuiltInRuleApp(app, goal, forced);
      }
      else {
         IBuiltInRuleApp result = customiaztion.completeBuiltInRuleApp(app, goal, forced);
         if (result != null) {
            if (result.complete()) {
               return result;
            }
            else {
               return super.completeBuiltInRuleApp(result, goal, forced);
            }
         }
         else {
            return super.completeBuiltInRuleApp(app, goal, forced);
         }
      }
   }

   /**
    * Instances of this class can be used to customize the behavior of a {@link CustomUserInterface}.
    * @author Martin Hentschel
    */
   public static interface IUserInterfaceCustomization {
      /**
       * This method will be called to treat {@link UserInterface#completeAndApplyTacletMatch(ApplyTacletDialogModel[], Goal)}.
       */
      public void completeAndApplyTacletMatch(ApplyTacletDialogModel[] models, Goal goal);

      /**
       * This method will be called to treat {@link UserInterface#completeBuiltInRuleApp(IBuiltInRuleApp, Goal, boolean)}.
       */
      public IBuiltInRuleApp completeBuiltInRuleApp(IBuiltInRuleApp app, Goal goal, boolean forced);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public ProofEnvironment createProofEnvironmentAndRegisterProof(ProofOblInput proofOblInput, ProofAggregate proofList, InitConfig initConfig) {
      //TODO: Find out why the proof has to be registered. This method should just return null and do nothing.
      initConfig.getServices().getSpecificationRepository().registerProof(proofOblInput, proofList.getFirstProof());
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean selectProofObligation(InitConfig initConfig) {
      return false; // Not supported.
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeProof(Proof proof) {
      proof.dispose();
   }

   @Override
   public synchronized void startAndWaitForAutoMode(Proof proof) {
      if (!isInAutoMode()) {
         autoModeThread = new AutoModeThread(proof);
         autoModeThread.run();
      }
   }

   @Override
   public synchronized void startAutoMode(Proof proof, ImmutableList<Goal> goals) {
      if (!isInAutoMode()) {
         autoModeThread = new AutoModeThread(proof, goals);
         autoModeThread.start();
      }
   }

   @Override
   public synchronized void startAutoMode(Proof proof) {
      if (!isInAutoMode()) {
         autoModeThread = new AutoModeThread(proof);
         autoModeThread.start();
      }
   }

   @Override
   public synchronized void stopAutoMode() {
      if (isInAutoMode()) {
         autoModeThread.cancel();
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
   public synchronized boolean isInAutoMode() {
      return autoModeThread != null;
   }

   private class AutoModeThread extends Thread {
      private final Proof proof;
      
      private final ImmutableList<Goal> goals;

      public AutoModeThread(Proof proof) {
         this(proof, null);
      }

      public AutoModeThread(Proof proof, ImmutableList<Goal> goals) {
         this.proof = proof;
         this.goals = goals;
      }

      @Override
      public void run() {
         try {
            fireAutoModeStarted(new ProofEvent(proof));
            ProofStarter starter = new ProofStarter(getListener(), false);
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
      
      public void cancel() {
         stop(); // Stop the currently running thread // TODO: Find better solution (REFACTORING_FIX_ME)
         autoModeThread = null;
         fireAutoModeStopped(new ProofEvent(proof));
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addAutoModeListener(AutoModeListener p) {
      if (p != null) {
         autoModeListener.add(p);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeAutoModeListener(AutoModeListener p) {
      if (p != null) {
         autoModeListener.remove(p);
      }
   }

   /**
    * fires the event that automatic execution has started
    */
   protected void fireAutoModeStarted(ProofEvent e) {
      AutoModeListener[] listener = autoModeListener.toArray(new AutoModeListener[autoModeListener.size()]);
      for (AutoModeListener aListenerList : listener) {
         aListenerList.autoModeStarted(e);
      }
   }

   /**
    * fires the event that automatic execution has stopped
    */
   protected void fireAutoModeStopped(ProofEvent e) {
      AutoModeListener[] listener = autoModeListener.toArray(new AutoModeListener[autoModeListener.size()]);
      for (AutoModeListener aListenerList : listener) {
         aListenerList.autoModeStopped(e);
      }
   }

   @Override
   public void taskFinished(TaskFinishedInfo info) {
      // Nothing to do
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void taskStarted(String message, int size) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void proofRegistered(ProofEnvironmentEvent event) {
      // Nothing to do  
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void progressStarted(Object sender) {
      // Nothing to do
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void progressStopped(Object sender) {
      // Nothing to do
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void reportStatus(Object sender, String status, int progress) {
      // Nothing to do
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void reportStatus(Object sender, String status) {
      // Nothing to do
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void resetStatus(Object sender) {
      // Nothing to do
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void reportException(Object sender, ProofOblInput input, Exception e) {
      // Nothing to do
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void taskProgress(int position) {
      // Nothing to do
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setProgress(int progress) {
      // Nothing to do
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setMaximum(int maximum) {
      // Nothing to do
   }
}