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
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

public class MethodBreakpointStopCondition extends AbstractLineBreakpointStopCondition {

   /**
    * flag to tell whether to stop on method entry
    */
   private boolean isEntry;
   
   /**
    * flag to tell whether to stop on method exit
    */
   private boolean isExit;

   /**
    * Creates a new {@link AbstractLineBreakpointStopCondition}.
    * 
    * @param classPath the path of the class the associated Breakpoint lies within
    * @param lineNumber the line where the associated Breakpoint is located in the class
    * @param hitCount the number of hits after which the execution should hold at this breakpoint
    * @param pm the {@link IProgramMethod} representing the Method which the Breakpoint is located at
    * @param proof the {@link Proof} that will be executed and should stop
    * @param parentCondition a {@link CompoundStopCondition} containing this {@link LineBreakpointStopCondition} and all other {@link LineBreakpointStopCondition} the associated {@link Proof} should use
    * @param condition the condition as given by the user
    * @param enabled flag if the Breakpoint is enabled
    * @param conditionEnabled flag if the condition is enabled
    * @param methodStart the line the containing method of this breakpoint starts at
    * @param methodEnd the line the containing method of this breakpoint ends at
    * @param containerType the type of the element containing the breakpoint
    * @param isEntry flag to tell whether to stop on method entry
    * @param isExit flag to tell whether to stop on method exit
    * @throws SLTranslationException if the condition could not be parsed to a valid Term
    */
   public MethodBreakpointStopCondition(String classPath, int lineNumber,
         int hitCount, IProgramMethod pm,
         Proof proof, CompoundStopCondition parentCondition, String condition,
         boolean enabled, boolean conditionEnabled, int methodStart,
         int methodEnd, boolean isEntry, boolean isExit) throws SLTranslationException {
      super(classPath, lineNumber, hitCount, pm, proof, parentCondition,
               condition, enabled, conditionEnabled, methodStart, methodEnd, pm.getContainerType());
      this.isEntry = isEntry;
      this.isExit = isExit;
   }
   
   @Override
   protected boolean breakpointHit(int line, String path, RuleApp ruleApp,
         Proof proof, Node node) throws ProofInputException {
      return ((isMethodCallNode(node, ruleApp)&&isEntry)||(isMethodReturnNode(node, ruleApp)&&isExit))&&super.breakpointHit(line, path, ruleApp, proof, node);
   }

   /**
    * @param node to check
    * @param ruleApp the applied rule app
    * @return true if the node represents a method call
    */
   private boolean isMethodCallNode(Node node, RuleApp ruleApp){
      SourceElement statement = NodeInfo.computeActiveStatement(ruleApp);
      IProgramMethod currentPm=null;
      if (statement instanceof MethodBodyStatement) {
         MethodBodyStatement mbs = (MethodBodyStatement)statement;
         currentPm = mbs.getProgramMethod(getProof().getServices()); 
      }
      if(SymbolicExecutionUtil.isMethodCallNode(node, ruleApp, NodeInfo.computeActiveStatement(ruleApp))&&currentPm != null&&currentPm.equals(getPm())){
            return true;
      }
      return false;
      
   }
   
   /**
    * @param node to check
    * @param ruleApp the applied rule app
    * @return true if the node represents a method return
    */
   private boolean isMethodReturnNode(Node node, RuleApp ruleApp){
      if(SymbolicExecutionUtil.isMethodReturnNode(node, ruleApp)
            &&isInScope(node)){
            return true;
      }
      return false;
      
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
            if(getVarsForCondition()!=null&&ruleApp!=null&&node!=null){
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
                              if(((isMethodCallNode(node, ruleApp)&&isEntry)||(isMethodReturnNode(node, ruleApp)&&isExit))&&isEnabled()&&(!isConditionEnabled()||conditionMet(ruleApp, proof, node))){
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
