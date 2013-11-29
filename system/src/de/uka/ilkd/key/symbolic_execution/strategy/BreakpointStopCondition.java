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

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;

import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.gui.ApplyStrategy.SingleRuleApplicationInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Node.NodeIterator;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

public abstract class BreakpointStopCondition implements IStopCondition {
   
   /**
    * The flag if the Breakpoint is enabled.
    */
   private boolean enabled;
   
   /**
    * The proof this stop condition is associated with
    */
   private Proof proof;
   
   /**
    * Saves all {@link Goal}s that were responsible for a breakpoint to trigger.
    */
   private LinkedHashSet<Goal> breakpointGoals = new LinkedHashSet<Goal>();
   
   /**
    * Stores for each {@link Node} which is a symbolic execution tree node the computed result
    * of {@link #isGoalAllowed(int, long, Proof, IGoalChooser, long, int, Goal)} to make
    * sure that it is only computed once and that the number of executed set statements is
    * not increased multiple times for the same {@link Node}.
    */
   private Map<Node, Boolean> goalAllowedResultPerSetNode = new LinkedHashMap<Node, Boolean>();

   /**
    * Creates a new {@link BreakpointStopCondition}.
    * 
    * @param proof the {@link Proof} that will be executed and should stop
    * @param enabled flag if the Breakpoint is enabled
    */
   public BreakpointStopCondition(Proof proof, boolean enabled){
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
                     // Check if limit of set nodes of the current goal is exceeded
                     if (!getBreakpointGoals().contains(goal)) {
                           try{
                              if(isEnabled()&&isBreakpointHit(activeStatement, ruleApp, proof, node)){
                                 getBreakpointGoals().add(goal);
                                 getGoalAllowedResultPerSetNode().put(node, Boolean.FALSE);
                                 }
                           }catch(ProofInputException e){
                              //TODO
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
      // Check if a rule was applied
      if (singleRuleApplicationInfo != null) {
         // Get the node on which a rule was applied.
         Goal goal = singleRuleApplicationInfo.getGoal();
         Node node = goal.node();
         assert node.childrenCount() == 0; // Make sure that this is the current goal node
         Node updatedNode = node.parent();
         // Check if multiple branches where created.
         if (updatedNode.childrenCount() >= 2) {
            if (getBreakpointGoals().contains(goal)) {
               // Reuse number of set nodes for new created goals
               NodeIterator childIter = updatedNode.childrenIterator();
               while (childIter.hasNext()) {
                  Node next = childIter.next();
                  Goal nextGoal = next.proof().getGoal(next);
                  // Check if the current goal is a new one
                  if (nextGoal != goal) {
                     // New goal found, use the number of set nodes for it.
                     getBreakpointGoals().add(nextGoal);
                  }
               }
            }
         }
         RuleApp ruleApp = goal.getRuleAppManager().peekNext();
         if(ruleApp != null){
            if (SymbolicExecutionUtil.isSymbolicExecutionTreeNode(node, ruleApp)) {
               // Check if the result for the current node was already computed.
               Boolean value = getGoalAllowedResultPerSetNode().get(node);
               if (value == null) {
                  if (getBreakpointGoals().contains(goal)) {
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
    * @param activeStatement the activeStatement of the node
    * @param ruleApp the applied ruleapp
    * @param proof the current proof
    * @param node the current node
    * @return true if execution should hold
    * @throws ProofInputException
    */
   protected abstract boolean isBreakpointHit(SourceElement activeStatement, RuleApp ruleApp, Proof proof, Node node)throws ProofInputException;
   
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
   
   @Override
   public String getGoalNotAllowedMessage(int maxApplications, long timeout,
         Proof proof, IGoalChooser goalChooser, long startTime,
         int countApplied, Goal goal) {
      return "Breakpoint hit!";
   }
   @Override
   public int getMaximalWork(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser) {
      getBreakpointGoals().clear(); // Reset number of already detected symbolic execution tree nodes for all goals.
      getGoalAllowedResultPerSetNode().clear(); // Remove no longer needed references.
      return 0;
   }
   @Override
   public String getStopMessage(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied,
         SingleRuleApplicationInfo singleRuleApplicationInfo) {
      return "Breakpoint hit!";
   }

   /**
    * @return the goalAllowedResultPerSetNode
    */
   public Map<Node, Boolean> getGoalAllowedResultPerSetNode() {
      return goalAllowedResultPerSetNode;
   }

   /**
    * @param goalAllowedResultPerSetNode the goalAllowedResultPerSetNode to set
    */
   public void setGoalAllowedResultPerSetNode(
         Map<Node, Boolean> goalAllowedResultPerSetNode) {
      this.goalAllowedResultPerSetNode = goalAllowedResultPerSetNode;
   }

   /**
    * @return the breakpointGoals
    */
   public LinkedHashSet<Goal> getBreakpointGoals() {
      return breakpointGoals;
   }

   /**
    * @param breakpointGoals the breakpointGoals to set
    */
   public void setBreakpointGoals(
         LinkedHashSet<Goal> breakpointGoals) {
      this.breakpointGoals = breakpointGoals;
   }
}
