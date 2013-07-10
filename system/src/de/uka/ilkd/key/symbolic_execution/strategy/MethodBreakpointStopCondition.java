package de.uka.ilkd.key.symbolic_execution.strategy;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

public class MethodBreakpointStopCondition extends AbstractBreakpointStopCondition {

   private boolean isEntry;
   
   private boolean isExit;

   public MethodBreakpointStopCondition(String classPath, int lineNumber,
         int hitCount, KeYEnvironment<?> environment, IProgramMethod pm,
         Proof proof, CompoundStopCondition parentCondition, String condition,
         boolean enabled, boolean conditionEnabled, int methodStart,
         int methodEnd, boolean isEntry, boolean isExit) throws SLTranslationException {
      super(classPath, lineNumber, hitCount, environment, pm, proof, parentCondition,
               condition, enabled, conditionEnabled, methodStart, methodEnd);
      this.isEntry = isEntry;
      this.isExit = isExit;
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
            if(varsForCondition!=null&&ruleApp!=null&&node!=null){
               refreshVarMaps(ruleApp, node);
            }
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
                     if (executedNumberOfSetNodes.intValue() + 1 > getMaximalNumberOfSetNodesToExecutePerGoal()) {
                        getGoalAllowedResultPerSetNode().put(node, Boolean.FALSE);
                        return false; // Limit of set nodes of this goal exceeded
                     }
                     else {
                           try {
                              if(((isMethodCallNode(node, ruleApp)&&isEntry)||(isMethodReturnNode(node, ruleApp)&&isExit))&&enabled&&(!conditionEnabled||conditionMet(ruleApp, proof, node))){
                                 // Increase number of set nodes on this goal and allow rule application
                                 if(hitcountExceeded(node)){
                                    executedNumberOfSetNodes = Integer.valueOf(executedNumberOfSetNodes.intValue() + 1);
                                    getExecutedNumberOfSetNodesPerGoal().put(goal, executedNumberOfSetNodes);
                                    getGoalAllowedResultPerSetNode().put(node, Boolean.TRUE);
                                 }
                                 }
                           }
                           catch (ProofInputException e) {
                              // TODO Auto-generated catch block
                              e.printStackTrace();
                           }
                        
                        return true; 
                     }
                  }
                  else {
                     // Reuse already computed result.
                     return value.booleanValue();
                  }
               }
            
         }
      return true;
   }
   
   private boolean isMethodCallNode(Node node, RuleApp ruleApp){
      SourceElement statement = NodeInfo.computeActiveStatement(ruleApp);
      IProgramMethod currentPm=null;
      if (statement instanceof MethodBodyStatement) {
         MethodBodyStatement mbs = (MethodBodyStatement)statement;
         currentPm = mbs.getProgramMethod(environment.getServices()); 
      }
      if(SymbolicExecutionUtil.isMethodCallNode(node, ruleApp, NodeInfo.computeActiveStatement(ruleApp))&&currentPm != null&&currentPm.equals(pm)){
            return true;
      }
      return false;
      
   }
   
   private boolean isMethodReturnNode(Node node, RuleApp ruleApp){
      if(SymbolicExecutionUtil.isMethodReturnNode(node, ruleApp)
            &&isInScope(node)){
            return true;
      }
      return false;
      
   }

   @Override
   protected StatementBlock getStatementBlock(
         StatementContainer statementContainer) {
      return (StatementBlock) statementContainer;
   }
   
   public boolean isEntry() {
      return isEntry;
   }

   public void setEntry(boolean isEntry) {
      this.isEntry = isEntry;
   }

   public boolean isExit() {
      return isExit;
   }

   public void setExit(boolean isExit) {
      this.isExit = isExit;
   }
}
