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

import de.uka.ilkd.key.gui.ApplyStrategy.SingleRuleApplicationInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

public abstract class AbstractBreakpointStopCondition extends
      ExecutedSymbolicExecutionTreeNodesStopCondition {
   
   /**
    * The flag if the Breakpoint is enabled.
    */
   private boolean enabled;
   
   /**
    * The proof this stop condition is associated with
    */
   private Proof proof;

   protected boolean stopAllGoals;

   /**
    * Creates a new {@link AbstractBreakpointStopCondition}.
    * 
    * @param proof the {@link Proof} that will be executed and should stop
    * @param enabled flag if the Breakpoint is enabled
    */
   public AbstractBreakpointStopCondition(Proof proof, boolean enabled){
      super();
      this.enabled=enabled;
      this.setProof(proof);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isGoalAllowed(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied, Goal goal) { 
         if(goal!=null){
            Node node = goal.node();
            RuleApp ruleApp = goal.getRuleAppManager().peekNext();
            SourceElement activeStatement = NodeInfo.computeActiveStatement(ruleApp);
               if (SymbolicExecutionUtil.isSymbolicExecutionTreeNode(node, ruleApp)) {
                  // Check if the result for the current node was already computed.
                  Boolean value = getGoalAllowedResultPerSetNode().get(node);
                  if (value == null) {
                     // Get the number of executed set nodes on the current goal
                     Integer executedNumberOfSetNodes = getExecutedNumberOfSetNodesPerGoal().get(goal);
                     if (executedNumberOfSetNodes == null) {
                        executedNumberOfSetNodes = Integer.valueOf(0);
                     }
                     // Check if limit of set nodes of the current goal is exceeded
                     if (!(executedNumberOfSetNodes.intValue() + 1 > getMaximalNumberOfSetNodesToExecutePerGoal())) {
                        activeStatement = NodeInfo.computeActiveStatement(ruleApp);
                        if (activeStatement != null && activeStatement.getStartPosition().getLine() != -1) {
                           String path = activeStatement.getPositionInfo().getParentClass();
                           int startLine = activeStatement.getStartPosition().getLine();
                           int endLine = activeStatement.getEndPosition().getLine();
                           try{
                              if(breakpointHit(startLine, endLine, path, ruleApp, proof, node)){
                                 // Increase number of set nodes on this goal and allow rule application
                                 executedNumberOfSetNodes = Integer.valueOf(executedNumberOfSetNodes.intValue() + 1);
                                 getExecutedNumberOfSetNodesPerGoal().put(goal, executedNumberOfSetNodes);
                                 getGoalAllowedResultPerSetNode().put(node, Boolean.FALSE);
                                 }
                           }catch(ProofInputException e){
                              //TODO
                           }
                        }
                        return true; 
                     }
                  }
               }
            
         }
      return true;
   }

   @Override
   public boolean shouldStop(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied,
         SingleRuleApplicationInfo singleRuleApplicationInfo) {
      // TODO Auto-generated method stub
      super.shouldStop(maxApplications, timeout, proof, goalChooser,
            startTime, countApplied, singleRuleApplicationInfo);
   // Check if a rule was applied
      if (singleRuleApplicationInfo != null) {
         // Get the node on which a rule was applied.
         Goal goal = singleRuleApplicationInfo.getGoal();
         Node node = goal.node();
         RuleApp ruleApp = goal.getRuleAppManager().peekNext();
         if(ruleApp != null && goal != null && node != null){
            if (SymbolicExecutionUtil.isSymbolicExecutionTreeNode(node, ruleApp)) {
               // Check if the result for the current node was already computed.
               Boolean value = getGoalAllowedResultPerSetNode().get(node);
               if (value == null) {
                  // Get the number of executed set nodes on the current goal
                  Integer executedNumberOfSetNodes = getExecutedNumberOfSetNodesPerGoal().get(goal);
                  if (executedNumberOfSetNodes == null) {
                     executedNumberOfSetNodes = Integer.valueOf(0);
                  }
                  if (executedNumberOfSetNodes.intValue() + 1 > getMaximalNumberOfSetNodesToExecutePerGoal()) {
                     getGoalAllowedResultPerSetNode().put(node, Boolean.TRUE);
                     return true; // Limit of set nodes of this goal exceeded
                  }
               }
               else {
                  // Reuse already computed result.
                  return value.booleanValue();
               }
            }
         }
      }
      return false;
   }
   
   /**
    * Determines whether the execution should stop with the given parameters
    * 
    * @param startLine the start line of the currently executed statement
    * @param endLine the end line
    * @param path the path of the class of the currently executed statement
    * @param ruleApp the applied ruleapp
    * @param proof the current proof
    * @param node the current node
    * @return true if execution should hold
    * @throws ProofInputException
    */
   protected boolean breakpointHit(int startLine, int endLine, String path, RuleApp ruleApp, Proof proof, Node node)throws ProofInputException {
      return enabled;
   }
   
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

   /**
    * @param proof the proof to set
    */
   public void setProof(Proof proof) {
      this.proof = proof;
   }
}
