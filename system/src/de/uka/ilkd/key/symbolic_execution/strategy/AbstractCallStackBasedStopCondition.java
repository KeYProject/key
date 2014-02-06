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

import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.gui.ApplyStrategy.SingleRuleApplicationInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Provides the basic functionality for {@link IStopCondition}s which stops
 * the auto mode when the call stack size of the starting set node has
 * a special difference to the call stack size of the current set node, e.g.
 * "step over" or "step return".
 * @author Martin Hentschel
 * @see StepOverSymbolicExecutionTreeNodesStopCondition
 * @see StepReturnSymbolicExecutionTreeNodesStopCondition
 */
public abstract class AbstractCallStackBasedStopCondition implements IStopCondition {
   /**
    * Maps a {@link Goal} to the initial call stack size at which the auto mode was started.
    */
   private Map<Goal, NodeStartEntry> startingCallStackSizePerGoal = new LinkedHashMap<Goal, NodeStartEntry>();

   /**
    * {@inheritDoc}
    */
   @Override
   public int getMaximalWork(int maxApplications, 
                             long timeout, 
                             Proof proof, 
                             IGoalChooser goalChooser) {
      startingCallStackSizePerGoal.clear(); // Reset initial call stack size of all goals. Will be filled in isGoalAllowed.
      return 0; // Return unknown because there is no relation between applied rules and step over functionality.
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
            // Check if goal is treated the first time
            NodeStartEntry startingCallStackSizeEntry = startingCallStackSizePerGoal.get(goal);
            if (startingCallStackSizeEntry == null) {
               Node parentSetNode = SymbolicExecutionUtil.findParentSetNode(node);
               int startingCallStackSize = SymbolicExecutionUtil.computeStackSize(parentSetNode != null ? parentSetNode.getAppliedRuleApp() : null);
               startingCallStackSizeEntry = new NodeStartEntry(node, startingCallStackSize);
               startingCallStackSizePerGoal.put(goal, startingCallStackSizeEntry);
               return true; // Initial check, no need to stop
            }
            else {
               if (node != startingCallStackSizeEntry.getNode()) {
                  // Check if current call stack size matches the end condition
                  int currentCallStackSize = SymbolicExecutionUtil.computeStackSize(ruleApp);
                  if (isCallStackSizeReached(startingCallStackSizeEntry.getNodeCallStackSize(), currentCallStackSize)) {
                     // Get parent node to make sure that already one node was executed which does not match the end condition
                     Node parentSetNode = SymbolicExecutionUtil.findParentSetNode(node);
                     int parentStackSize = SymbolicExecutionUtil.computeStackSize(parentSetNode.getAppliedRuleApp());
                     if (isCallStackSizeReached(startingCallStackSizeEntry.getNodeCallStackSize(), parentStackSize)) {
                        // Parent node also don't fulfill the call stack limit, stop now
                        return false;
                     }
                     else {
                        // Parent node is deeper in call stack, so continue
                        return true;
                     }
                  }
                  else {
                     // Currently deeper in call stack, continue
                     return true;
                  }
               }
               else {
                  return true; // Initial node
               }
            }
         }
         else {
            // Internal proof node, allow rule
            return true;
         }
      }
      else {
         return true; // Allowed, because ApplyStrategy will handle the null case
      }
   }
   
   /**
    * Checks if the call stack size limit is reached.
    * @param initialCallStackSize The call stack size of the initial set node.
    * @param currentCallStackSize The call stack size of the current set node.
    * @return {@code true} limit reached, {@code false} limit node reached.
    */
   protected abstract boolean isCallStackSizeReached(int initialCallStackSize, int currentCallStackSize);

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
            // If an initial call stack size is available for the goal it must be used for all other new created goals.
            NodeStartEntry startingCallStackSizeValue = startingCallStackSizePerGoal.get(goal);
            if (startingCallStackSizeValue != null) {
               // Reuse initial call stack size for new created goals
               Iterator<Node> childIter = updatedNode.childrenIterator();
               while (childIter.hasNext()) {
                  Node next = childIter.next();
                  Goal nextGoal = next.proof().getGoal(next);
                  // Check if the current goal is a new one
                  if (nextGoal != goal) {
                     // New goal found, use the initial call stack size for it.
                     startingCallStackSizePerGoal.put(nextGoal, startingCallStackSizeValue);
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
    * Instances of this class are used in 
    * {@link AbstractCallStackBasedStopCondition#startingCallStackSizePerGoal}
    * to represent the initial {@link Node} of {@link Goal} on which
    * the auto mode was started together with its call stack size.
    * @author Martin Hentschel
    */
   private static class NodeStartEntry {
      /**
       * The initial {@link Node} of a {@link Goal} on that the auto mode was started.
       */
      private Node node;
      
      /**
       * The call stack size of {@link #node}.
       */
      private int nodeCallStackSize;

      /**
       * Constructor.
       * @param node The initial {@link Node} of a {@link Goal} on that the auto mode was started.
       * @param nodeCallStackSize The call stack size of {@link #node}.
       */
      public NodeStartEntry(Node node, int nodeCallStackSize) {
         super();
         this.node = node;
         this.nodeCallStackSize = nodeCallStackSize;
      }

      /**
       * Returns the initial {@link Node} of a {@link Goal} on that the auto mode was started.
       * @return The initial {@link Node} of a {@link Goal} on that the auto mode was started.
       */
      public Node getNode() {
         return node;
      }

      /**
       * Returns the call stack size of {@link #getNode()}.
       * @return The call stack size of {@link #getNode()}.
       */
      public int getNodeCallStackSize() {
         return nodeCallStackSize;
      }
   }
}
