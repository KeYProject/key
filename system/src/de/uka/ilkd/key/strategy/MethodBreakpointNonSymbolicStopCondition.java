package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.gui.ApplyStrategy.SingleRuleApplicationInfo;
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
import de.uka.ilkd.key.symbolic_execution.strategy.AbstractLineBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

public class MethodBreakpointNonSymbolicStopCondition extends AbstractNonSymbolicLineBreakpointStopCondition {

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
    * @param parentCondition a {@link CompoundStopCondition} containing this {@link LineBreakpointNonSymbolicStopCondition} and all other {@link LineBreakpointNonSymbolicStopCondition} the associated {@link Proof} should use
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
   public MethodBreakpointNonSymbolicStopCondition(String classPath, int lineNumber,
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
   protected boolean breakpointHit(int startLine, int endLine, String path, RuleApp ruleApp,
         Proof proof, Node node) throws ProofInputException {
      return ((isMethodCallNode(node, ruleApp)&&isEntry)||(isMethodReturnNode(node, ruleApp)&&isExit))&&super.breakpointHit(startLine, endLine, path, ruleApp, proof, node);
   } 
   
   @Override
   public boolean shouldStop(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied,
         SingleRuleApplicationInfo singleRuleApplicationInfo) { 
      try{
         if (singleRuleApplicationInfo != null) {
            Goal goal = singleRuleApplicationInfo.getGoal();
            Node node = goal.node();
            RuleApp ruleApp = singleRuleApplicationInfo.getAppliedRuleApp();
            if(((isMethodCallNode(node, ruleApp)&&isEntry)||(isMethodReturnNode(node, ruleApp)&&isExit))&&isEnabled()&&(!isConditionEnabled()||conditionMet(ruleApp, proof, node))&&hitcountExceeded(node)){
               return true;
            }
         }
      }catch(ProofInputException e){
         //TODO
      }
      return false;
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
            &&isCorrectMethodReturn(node, ruleApp)){
            return true;
      }
      return false;
      
   }
   
   private boolean isCorrectMethodReturn(Node node, RuleApp ruleApp){
      Node checkNode = node.parent();
      int innerMethodCount = 0;
      while (checkNode != null) {
         SourceElement activeStatement = NodeInfo.computeActiveStatement(checkNode.getAppliedRuleApp());
         if(SymbolicExecutionUtil.isMethodReturnNode(checkNode, checkNode.getAppliedRuleApp())){
            innerMethodCount++;
         }
         if (SymbolicExecutionUtil.isMethodCallNode(checkNode, checkNode.getAppliedRuleApp(), activeStatement)) {
            IProgramMethod currentPm=null;
            if (activeStatement instanceof MethodBodyStatement) {
               MethodBodyStatement mbs = (MethodBodyStatement)activeStatement;
               currentPm = mbs.getProgramMethod(getProof().getServices()); 
               if (currentPm!=null&&currentPm.equals(getPm())) {
                  return true;
               }else{
                  if(innerMethodCount==0){
                     return false;
                  }else{
                     innerMethodCount--;
                  }
               }
            }
         }
         checkNode = checkNode.parent();
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
