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

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.gui.ApplyStrategy.SingleRuleApplicationInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * <p>
 * This {@link IStopCondition} stops the auto mode ({@link ApplyStrategy}) if
 * a given number ({@link #getMaximalNumberOfSetNodesToExecutePerGoal()}) of maximal
 * executed symbolic execution tree nodes is reached in a goal. 
 * </p>
 * <p>
 * If a {@link Node} in
 * KeY's proof tree is also a node in a symbolic execution tree is computed
 * via {@link SymbolicExecutionUtil#isSymbolicExecutionTreeNode(Node)}.
 * </p>
 * <p>
 * The auto mode is stopped exactly in the open goal {@link Node} which
 * will become the next symbolic execution tree node.
 * </p>
 * @author Martin Hentschel
 */
public class ExecutedSymbolicExecutionTreeNodesStopCondition implements IStopCondition {
   /**
    * The default maximal number of steps to simulate a complete program execution.
    */
   public static final int MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN = 1000;

   /**
    * The default maximal number of steps to do exactly one step in each goal.
    */
   public static final int MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_FOR_ONE_STEP = 1;

   /**
    * The maximal number of allowed symbolic execution tree nodes per goal.
    * The auto mode will stop exactly in the open goal proof node which
    * becomes the next symbolic execution tree node.
    */
   private int maximalNumberOfSetNodesToExecutePerGoal;
   
   /**
    * Maps a {@link Goal} to the number of executed symbolic execution tree nodes.
    */
   private Map<Goal, Integer> executedNumberOfSetNodesPerGoal = new LinkedHashMap<Goal, Integer>();
   
   /**
    * Stores for each {@link Node} which is a symbolic execution tree node the computed result
    * of {@link #isGoalAllowed(int, long, Proof, IGoalChooser, long, int, Goal)} to make
    * sure that it is only computed once and that the number of executed set statements is
    * not increased multiple times for the same {@link Node}.
    */
   private Map<Node, Boolean> goalAllowedResultPerSetNode = new LinkedHashMap<Node, Boolean>();
   
   /**
    * Constructor to stop after one executed symbolic execution tree node.
    */
   public ExecutedSymbolicExecutionTreeNodesStopCondition() {
      this(1);
   }

   /**
    * Constructor to stop after the given number of symbolic execution tree nodes.
    * @param maximalNumberOfSetNodesToExecutePerGoal The maximal number of allowed symbolic execution tree nodes per goal.
    */
   public ExecutedSymbolicExecutionTreeNodesStopCondition(int maximalNumberOfSetNodesToExecutePerGoal) {
      this.maximalNumberOfSetNodesToExecutePerGoal = maximalNumberOfSetNodesToExecutePerGoal;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getMaximalWork(int maxApplications, 
                             long timeout, 
                             Proof proof, 
                             IGoalChooser goalChooser) {
      executedNumberOfSetNodesPerGoal.clear(); // Reset number of already detected symbolic execution tree nodes for all goals.
      goalAllowedResultPerSetNode.clear(); // Remove no longer needed references.
      return 0; // Return unknown because there is no relation between applied rules and executed symbolic execution tree nodes.
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isGoalAllowed(int maxApplications, 
                                long timeout, 
                                Proof proof, 
                                IGoalChooser goalChooser, 
                                long startTime, 
                                int countApplied, 
                                Goal goal) {
      if (goal != null) {
         Node node = goal.node();
         // Check if goal is allowed
         RuleApp ruleApp = goal.getRuleAppManager().peekNext();
         if (SymbolicExecutionUtil.isSymbolicExecutionTreeNode(node, ruleApp)) {
            // Check if the result for the current node was already computed.
            Boolean value = goalAllowedResultPerSetNode.get(node);
            if (value == null) {
               // Get the number of executed set nodes on the current goal
               Integer executedNumberOfSetNodes = executedNumberOfSetNodesPerGoal.get(goal);
               if (executedNumberOfSetNodes == null) {
                  executedNumberOfSetNodes = Integer.valueOf(0);
               }
               // Check if limit of set nodes of the current goal is exceeded
               if (executedNumberOfSetNodes.intValue() + 1 > maximalNumberOfSetNodesToExecutePerGoal) {
                  goalAllowedResultPerSetNode.put(node, Boolean.FALSE);
                  return false; // Limit of set nodes of this goal exceeded
               }
               else {
                  // Increase number of set nodes on this goal and allow rule application
                  executedNumberOfSetNodes = Integer.valueOf(executedNumberOfSetNodes.intValue() + 1);
                  executedNumberOfSetNodesPerGoal.put(goal, executedNumberOfSetNodes);
                  goalAllowedResultPerSetNode.put(node, Boolean.TRUE);
                  return true;
               }
            }
            else {
               // Reuse already computed result.
               return value.booleanValue();
            }
         }
         else {
            return true;
         }
      }
      else {
         return true; // Allowed, because ApplyStrategy will handle the null case
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getGoalNotAllowedMessage(int maxApplications, 
                                          long timeout, 
                                          Proof proof, 
                                          IGoalChooser goalChooser, 
                                          long startTime, 
                                          int countApplied, 
                                          Goal goal) {
      if (maximalNumberOfSetNodesToExecutePerGoal > 1) {
         return "Maximal limit of " + maximalNumberOfSetNodesToExecutePerGoal + " symbolic execution tree nodes reached.";
      }
      else {
         return "Maximal limit of one symbolic execution tree node reached.";
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean shouldStop(int maxApplications, 
                             long timeout, 
                             Proof proof, 
                             IGoalChooser goalChooser, 
                             long startTime, 
                             int countApplied, 
                             SingleRuleApplicationInfo singleRuleApplicationInfo) {
      // Check if a rule was applied
      if (singleRuleApplicationInfo != null) {
         // Get the node on which a rule was applied.
         Goal goal = singleRuleApplicationInfo.getGoal();
         Node goalNode = goal.node();
         assert goalNode.childrenCount() == 0; // Make sure that this is the current goal node
         Node updatedNode = goalNode.parent();
         // Check if multiple branches where created.
         if (updatedNode.childrenCount() >= 2) {
            // If a number of executed set nodes is available for the goal it must be used for all other new created goals.
            Integer executedValue = executedNumberOfSetNodesPerGoal.get(goal);
            if (executedValue != null) {
               // Reuse number of set nodes for new created goals
                Iterator<Node> childIter = updatedNode.childrenIterator();
               while (childIter.hasNext()) {
                  Node next = childIter.next();
                  Goal nextGoal = next.proof().getGoal(next);
                  // Check if the current goal is a new one
                  if (nextGoal != goal) {
                     // New goal found, use the number of set nodes for it.
                     executedNumberOfSetNodesPerGoal.put(nextGoal, executedValue);
                  }
               }
            }
         }
      }
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getStopMessage(int maxApplications, 
                                long timeout, 
                                Proof proof, 
                                IGoalChooser goalChooser, 
                                long startTime, 
                                int countApplied, 
                                SingleRuleApplicationInfo singleRuleApplicationInfo) {
      return null;
   }

   /**
    * Returns the maximal number of executed symbolic execution tree nodes per goal per auto mode run.
    * @return The maximal number of executed symbolic execution tree nodes per goal per auto mode run.
    */
   public int getMaximalNumberOfSetNodesToExecutePerGoal() {
      return maximalNumberOfSetNodesToExecutePerGoal;
   }
   
   /**
    * Sets the maximal number of executed symbolic execution tree nodes per goal per auto mode run.
    * @param maximalNumberOfSetNodesToExecute The maximal number of executed symbolic execution tree nodes per per goal auto mode run.
    */
   public void setMaximalNumberOfSetNodesToExecutePerGoal(int maximalNumberOfSetNodesToExecute) {
      this.maximalNumberOfSetNodesToExecutePerGoal = maximalNumberOfSetNodesToExecute;
   }
   
   /**
    * Checks if at least one symbolic execution tree node was executed.
    * @return {@code true} at least one symbolic execution tree node was executed, {@code false} no symbolic execution tree node was executed.
    */
   public boolean wasSetNodeExecuted() {
      return !executedNumberOfSetNodesPerGoal.isEmpty();
   }
   
   /**
    * Returns the number of executed symbolic execution tree nodes per {@link Goal}.
    * @return The number of executed symbolic execution tree nodes per {@link Goal}.
    */
   public Map<Goal, Integer> getExectuedSetNodesPerGoal() {
      return executedNumberOfSetNodesPerGoal;
   }
}