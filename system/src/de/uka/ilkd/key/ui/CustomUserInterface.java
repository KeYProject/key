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

import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.gui.ApplyTacletDialogModel;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.ProofEnvironmentEvent;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

/**
 * <p>
 * An extended version of {@link ConsoleUserInterface} which can be used
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
public class CustomUserInterface extends ConsoleUserInterface {
   /**
    * An optional {@link IUserInterfaceCustomization}.
    */
   private final IUserInterfaceCustomization customiaztion;
   
   /**
    * Constructor.
    * @param verbose Verbose?
    */
   public CustomUserInterface(boolean verbose) {
      this(verbose, null);
   }
   
   /**
    * Constructor.
    * @param verbose Verbose?
    * @param customiaztion An optional {@link IUserInterfaceCustomization}.
    */
   public CustomUserInterface(boolean verbose, IUserInterfaceCustomization customiaztion) {
      super(null, verbose);
      this.customiaztion = customiaztion;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void proofCreated(ProblemInitializer sender, ProofAggregate proofAggregate) {
      // Nothing to do
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
   public void taskStarted(String message, int size) {
      if(isVerbose()) {
         System.out.println("CustomConsoleUserInterface.taskStarted(" + message + "," + size + ")");
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void taskFinished(TaskFinishedInfo info) {
      if(isVerbose()) {
         System.out.println("CustomConsoleUserInterface.taskFinished()");
      }
      // Update selected node in KeYMediator. This is copied code from WindowUserInterface and should be refactored in the future
      if (info.getSource() instanceof ApplyStrategy) {
         resetStatus(this);
         ApplyStrategy.ApplyStrategyInfo result = (ApplyStrategyInfo) info.getResult();

         Proof proof = info.getProof();
         if (!proof.closed()) {
            Goal g = result.nonCloseableGoal();
            if (g == null) {
               g = proof.openGoals().head();
            }
            getMediator().goalChosen(g);
         }
      }
   }
   
   /**
    * {@inheritDoc}
    */   
   @Override
   public void completeAndApplyTacletMatch(ApplyTacletDialogModel[] models, Goal goal) {
      if (customiaztion != null) {
         customiaztion.completeAndApplyTacletMatch(models, goal);
      }
      else {
         super.completeAndApplyTacletMatch(models, goal);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IBuiltInRuleApp completeBuiltInRuleApp(IBuiltInRuleApp app, Goal goal, boolean forced) {
      if (customiaztion == null || getMediator().isInAutoMode()) {
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
    * {@inheritDoc}
    */
   @Override
   public ProofEnvironment createProofEnvironmentAndRegisterProof(ProofOblInput proofOblInput, ProofAggregate proofList, InitConfig initConfig) {
      //TODO: Find out why the proof has to be registered. This method should just return null and do nothing.
      initConfig.getServices().getSpecificationRepository().registerProof(proofOblInput, proofList.getFirstProof());
      return null;
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
}