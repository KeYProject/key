package de.uka.ilkd.key.symbolic_execution.strategy;

import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.gui.ApplyStrategy.SingleRuleApplicationInfo;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * <p>
 * This {@link IStopCondition} stops the auto mode ({@link ApplyStrategy}) if
 * a given number ({@link #getMaximalNumberOfSetNodesToExecute()}) of maximal
 * executed symbolic execution tree nodes is reached. 
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
    * The maximal number of allowed symbolic execution tree nodes.
    * The auto mode will stop exactly in the open goal proof node which
    * becomes the next symbolic exection tree node.
    */
   private int maximalNumberOfSetNodesToExecute;
   
   /**
    * The number of detected symbolic execution tree nodes in the currently
    * running auto mode. It is {@code -1} if this {@link IStopCondition} was never used.
    */
   private int executedNumberOfSetNodes = -1;
   
   /**
    * Constructor to stop after one executed symbolic execution tree node.
    */
   public ExecutedSymbolicExecutionTreeNodesStopCondition() {
      this(1);
   }

   /**
    * Constructor to stop after the given number of symbolic execution tree nodes.
    * @param maximalNumberOfSetNodesToExecute The maximal number of allowed symbolic execution tree nodes.
    */
   public ExecutedSymbolicExecutionTreeNodesStopCondition(int maximalNumberOfSetNodesToExecute) {
      this.maximalNumberOfSetNodesToExecute = maximalNumberOfSetNodesToExecute;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getMaximalWork(ApplyStrategy strategy, 
                             int maxApplications, 
                             long timeout, 
                             Proof proof, 
                             IGoalChooser goalChooser) {
      executedNumberOfSetNodes = -1; // Reset number of already detected symbolic execution tree nodes. It is initialized based on the current proof tree in shouldStop when the first node is provided.
      return 0; // Return unknown because there is no relation between applied rules and executed symbolic execution tree nodes.
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean shouldStop(ApplyStrategy strategy, 
                             int maxApplications, 
                             long timeout, 
                             Proof proof, 
                             IGoalChooser goalChooser, 
                             long startTime, 
                             int countApplied, 
                             SingleRuleApplicationInfo singleRuleApplicationInfo) {
      if (singleRuleApplicationInfo != null) {
         // Get open goal node on branch
         Node node = singleRuleApplicationInfo.getGoal().node();
         // Check if auto mode was started and must be initialized
         if (executedNumberOfSetNodes < 0) {
            Node parent = node.parent();
            if (SymbolicExecutionUtil.isSymbolicExecutionTreeNode(parent, parent.getAppliedRuleApp())) {
               executedNumberOfSetNodes = 1; // Last open goal was a symbolic execution tree node. 
            }
            else {
               executedNumberOfSetNodes = 0; // Last stop was somewhere in between symbolic execution tree nodes
            }
         }
         // Get rule app which will be applied on it in the future
         RuleApp ruleApp = singleRuleApplicationInfo.getGoal().getRuleAppManager().peekNext();
         if(SymbolicExecutionUtil.isSymbolicExecutionTreeNode(node, ruleApp)) {
            executedNumberOfSetNodes ++;
            if (executedNumberOfSetNodes > maximalNumberOfSetNodesToExecute) {
               return true; // TODO: Continue on all other branches before stop, maybe use own IGoalChooser
            }
            else {
               return false; // Still more symbolic execution tree nodes allowed.
            }
         }
         else {
            return false; // Internal node, continue
         }
      }
      else {
         return false; // Initial check, should continue because nothing done yet.
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getStopMessage(ApplyStrategy strategy, 
                                int maxApplications, 
                                long timeout, 
                                Proof proof, 
                                IGoalChooser goalChooser, 
                                long startTime, 
                                int countApplied, 
                                SingleRuleApplicationInfo singleRuleApplicationInfo) {
      if (maximalNumberOfSetNodesToExecute > 1) {
         return "Maximal limit of " + maximalNumberOfSetNodesToExecute + " symbolic execution tree nodes reached.";
      }
      else {
         return "Maximal limit of one symbolic execution tree node reached.";
      }
   }

   /**
    * Returns the maximal number of executed symbolic execution tree nodes per auto mode run.
    * @return The maximal number of executed symbolic execution tree nodes per auto mode run.
    */
   public int getMaximalNumberOfSetNodesToExecute() {
      return maximalNumberOfSetNodesToExecute;
   }
   
   /**
    * Sets the maximal number of executed symbolic execution tree nodes per auto mode run.
    * @param maximalNumberOfSetNodesToExecute The maximal number of executed symbolic execution tree nodes per auto mode run.
    */
   public void setMaximalNumberOfSetNodesToExecute(int maximalNumberOfSetNodesToExecute) {
      this.maximalNumberOfSetNodesToExecute = maximalNumberOfSetNodesToExecute;
   }

   /**
    * Returns the number of executed symbolic execution tree nodes in the previous run.
    * @return The number of executed symbolic execution tree nodes in the previous run or {@code -1} if the {@link IStopCondition} was never used..
    */
   public int getExecutedNumberOfSetNodes() {
      return executedNumberOfSetNodes;
   }
}
