package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.LinkedHashMap;
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
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

public class test implements IStopCondition{ 
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
    * Creates a new {@link BreakpointStopCondition}.
    * 
    * @param proof the {@link Proof} that will be executed and should stop
    * @param enabled flag if the Breakpoint is enabled
    */
   public test(Proof proof, boolean enabled){
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
                     if (!(executedNumberOfSetNodes.intValue() > 0)) {
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

   /**
    * {@inheritDoc}
    */
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
            // If a number of executed set nodes is available for the goal it must be used for all other new created goals.
            Integer executedValue = getExecutedNumberOfSetNodesPerGoal().get(goal);
            if (executedValue != null) {
               // Reuse number of set nodes for new created goals
               NodeIterator childIter = updatedNode.childrenIterator();
               while (childIter.hasNext()) {
                  Node next = childIter.next();
                  Goal nextGoal = next.proof().getGoal(next);
                  // Check if the current goal is a new one
                  if (nextGoal != goal) {
                     // New goal found, use the number of set nodes for it.
                     getExecutedNumberOfSetNodesPerGoal().put(nextGoal, executedValue);
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
                  // Get the number of executed set nodes on the current goal
                  Integer executedNumberOfSetNodes = getExecutedNumberOfSetNodesPerGoal().get(goal);
                  if (executedNumberOfSetNodes == null) {
                     executedNumberOfSetNodes = Integer.valueOf(0);
                  }
                  if (executedNumberOfSetNodes.intValue() > 0) {
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

   /**
    * @return the executedNumberOfSetNodesPerGoal
    */
   public Map<Goal, Integer> getExecutedNumberOfSetNodesPerGoal() {
      return executedNumberOfSetNodesPerGoal;
   }

   /**
    * @param executedNumberOfSetNodesPerGoal the executedNumberOfSetNodesPerGoal to set
    */
   public void setExecutedNumberOfSetNodesPerGoal(
         Map<Goal, Integer> executedNumberOfSetNodesPerGoal) {
      this.executedNumberOfSetNodesPerGoal = executedNumberOfSetNodesPerGoal;
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
    * {@inheritDoc}
    */
   @Override
   public int getMaximalWork(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser) {
      return 0;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getGoalNotAllowedMessage(int maxApplications, long timeout,
         Proof proof, IGoalChooser goalChooser, long startTime,
         int countApplied, Goal goal) {
      return "Breakpoint hit!";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getStopMessage(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied,
         SingleRuleApplicationInfo singleRuleApplicationInfo) {
      return "Breakpoint hit!";
   }

}
