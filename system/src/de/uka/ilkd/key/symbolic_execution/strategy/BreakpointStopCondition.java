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

package de.uka.ilkd.key.symbolic_execution.strategy;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.RuleApp;

public abstract class BreakpointStopCondition extends ExecutedSymbolicExecutionTreeNodesStopCondition {
   /**
    * The flag if the Breakpoint is enabled.
    */
   private boolean enabled;
   
   /**
    * The proof this stop condition is associated with.
    */
   private final Proof proof;

   /**
    * Creates a new {@link BreakpointStopCondition}.
    * @param proof the {@link Proof} that will be executed and should stop
    * @param enabled flag if the Breakpoint is enabled
    */
   public BreakpointStopCondition(Proof proof, boolean enabled) {
      super(Integer.MAX_VALUE);
      this.proof = proof;
      this.enabled = enabled;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public int getMaximalWork(int maxApplications, 
                             long timeout, 
                             Proof proof, 
                             IGoalChooser goalChooser) {
      setMaximalNumberOfSetNodesToExecutePerGoal(Integer.MAX_VALUE);
      return super.getMaximalWork(maxApplications, timeout, proof, goalChooser);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleNodeLimitNotExceeded(int maxApplications, 
                                             long timeout, 
                                             Proof proof, 
                                             IGoalChooser goalChooser, 
                                             long startTime, 
                                             int countApplied, 
                                             Goal goal,
                                             Node node,
                                             RuleApp ruleApp,
                                             Integer executedNumberOfSetNodes) {
      super.handleNodeLimitNotExceeded(maxApplications, timeout, proof, goalChooser, startTime, countApplied, goal, node, ruleApp, executedNumberOfSetNodes);
      try {
         SourceElement activeStatement = NodeInfo.computeActiveStatement(ruleApp);
         if (isEnabled() && isBreakpointHit(activeStatement, ruleApp, proof, node)) {
            setMaximalNumberOfSetNodesToExecutePerGoal(executedNumberOfSetNodes.intValue());
         }
      }
      catch (ProofInputException e) {
      }
   }
   
   /**
    * Determines if the breakpoint represented by this BreakpointStopConition is triggered.
    * Override this method in order to suspend execution when a breakpoint is hit.
    * 
    * @param activeStatement the activeStatement of the node
    * @param ruleApp the applied ruleapp
    * @param proof the current proof
    * @param node the current node
    * @return true if execution should hold
    * @throws ProofInputException
    */
   protected abstract boolean isBreakpointHit(SourceElement activeStatement, 
                                              RuleApp ruleApp, 
                                              Proof proof, 
                                              Node node) throws ProofInputException;
   
   /**
    * Checks if the Breakpoint is enabled.
    * @return true if Breakpoint is enabled
    */
   public boolean isEnabled() {
      return enabled;
   }

   /**
    * Sets the new enabled value.
    * @param enabled the new value
    */
   public void setEnabled(boolean enabled) {
      this.enabled = enabled;
   }

   /**
    * @return the proof
    */
   public Proof getProof() {
      return proof;
   }
}
