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

package de.uka.ilkd.key.ui;

import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProblemInitializer;

/**
 * <p>
 * An extended version of {@link ConsoleUserInterface} which can be used
 * to prove manually instantiated proofs.
 * </p>
 * <p>
 * The basic usage is like:
 * <code><pre>
 * // Create user interface
 * CustomConsoleUserInterface ui = new CustomConsoleUserInterface(false);
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
public class CustomConsoleUserInterface extends ConsoleUserInterface {
   /**
    * Constructor.
    * @param verbose Verbose?
    */
   public CustomConsoleUserInterface(boolean verbose) {
      super(null, verbose);
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
}