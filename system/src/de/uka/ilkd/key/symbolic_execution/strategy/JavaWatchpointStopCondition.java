package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * This{@link JavaWatchpointStopCondition} represents a Java watchpoint and is responsible to tell the debugger to stop execution when the respective
 * variable is accessed or modified.
 * 
 * @author Marco Drebing
 */
public class JavaWatchpointStopCondition extends
      ExecutedSymbolicExecutionTreeNodesStopCondition {

   private boolean isAccess;

   private boolean isModification;

   private String fieldName;

   private boolean enabled;

   private KeYJavaType containerKJT;

   private String fullFieldName;
   
   private Map<Integer, Boolean> hittedNodes;
   
   /**
    * The HitCount of the Breakpoint (set by user).
    */
   private int hitCount;
   
   /**
    * Counter for how often the Breakpoint was hit.
    */
   private int hitted = 0;


   /**
    * Creates a new {@link JavaWatchpointStopCondition}.
    * 
    * @param enabled flag if the Breakpoint is enabled
    * @param hitCount the number of hits after which the execution should hold at this breakpoint
    * @param fieldName the field to watch
    * @param isAcces flag to watch for accesses
    * @param isModification flag to watch for modifications
    * @param containerType the type of the element containing the breakpoint
    * @param proof the {@link Proof} that will be executed and should stop
    */
   public JavaWatchpointStopCondition(boolean enabled, int hitCount, String fieldName, boolean isAcces,
         boolean isModification, KeYJavaType containerKJT, Proof proof) {
      super();
      this.enabled = enabled;
      this.isAccess = isAcces;
      this.isModification = isModification;
      this.fieldName = fieldName;
      this.containerKJT = containerKJT;
      this.fullFieldName = containerKJT.getSort().toString()+"::"+fieldName;
      this.hitCount = hitCount;
      hittedNodes=new HashMap<Integer, Boolean>();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isGoalAllowed(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied, Goal goal) {
      if (goal != null) {
         Node node = goal.node();
         RuleApp ruleApp = goal.getRuleAppManager().peekNext();
         
         if (SymbolicExecutionUtil.isSymbolicExecutionTreeNode(node, ruleApp)) {
            // Check if the result for the current node was already computed.
            Boolean value = getGoalAllowedResultPerSetNode().get(node);
            if (value == null) {
               // Get the number of executed set nodes on the current goal
               Integer executedNumberOfSetNodes = getExecutedNumberOfSetNodesPerGoal()
                     .get(goal);
               if (executedNumberOfSetNodes == null) {
                  executedNumberOfSetNodes = Integer.valueOf(0);
               }
               // Check if limit of set nodes of the current goal is exceeded
               if (executedNumberOfSetNodes.intValue() + 1 > getMaximalNumberOfSetNodesToExecutePerGoal()) {
                  getGoalAllowedResultPerSetNode().put(node, Boolean.FALSE);
                  return false; // Limit of set nodes of this goal exceeded
               }
               else {
                     if (enabled) {
                        SourceElement activeStatement = NodeInfo.computeActiveStatement(ruleApp);
                        if (activeStatement != null && activeStatement instanceof Assignment) {
                           Assignment assignment = (Assignment) activeStatement;
                           SourceElement firstElement = assignment.getFirstElement();
                           if(firstElement instanceof LocationVariable){
                              LocationVariable locVar = (LocationVariable)firstElement;
                              KeYJavaType containerType = locVar.getContainerType();
                              if(containerType!=null&&containerType.equals(containerKJT)&&fullFieldName.equals(locVar.toString())&&isModification&&hitcountExceeded(node)){
                                 // Increase number of set nodes on this goal and allow rule application
                                 executedNumberOfSetNodes = Integer.valueOf(executedNumberOfSetNodes.intValue() + 1);
                                 getExecutedNumberOfSetNodesPerGoal().put(goal, executedNumberOfSetNodes);
                                 getGoalAllowedResultPerSetNode().put(node, Boolean.TRUE);
                              }
                           }
                           if(checkChildrenOfSourceElement(assignment)&&hitcountExceeded(node)){
                              // Increase number of set nodes on this goal and allow rule application
                              executedNumberOfSetNodes = Integer.valueOf(executedNumberOfSetNodes.intValue() + 1);
                              getExecutedNumberOfSetNodesPerGoal().put(goal, executedNumberOfSetNodes);
                              getGoalAllowedResultPerSetNode().put(node, Boolean.TRUE);
                           }
                        }else if (activeStatement != null) {
                           if(checkChildrenOfSourceElement(activeStatement)&&hitcountExceeded(node)){
                              // Increase number of set nodes on this goal and allow rule application
                              executedNumberOfSetNodes = Integer.valueOf(executedNumberOfSetNodes.intValue() + 1);
                              getExecutedNumberOfSetNodesPerGoal().put(goal, executedNumberOfSetNodes);
                              getGoalAllowedResultPerSetNode().put(node, Boolean.TRUE);
                           }
                        }
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

   private boolean checkChildrenOfSourceElement(SourceElement sourceElement) {
      boolean found = false;
      if (sourceElement instanceof Assignment) {
         Assignment assignment = (Assignment) sourceElement;
         for (int i = 1; i < assignment.getChildCount(); i++) {
            SourceElement childElement = assignment.getChildAt(i);
            if (childElement.toString().equals(fieldName)&& childElement instanceof FieldReference) {
               FieldReference field = (FieldReference) childElement;
               ProgramVariable progVar = field.getProgramVariable();
               if (fullFieldName.equals(progVar.toString())) {
                  return isAccess;
               }
            }
            else if (childElement instanceof NonTerminalProgramElement) {
               found = found || checkChildrenOfSourceElement(childElement);
            }
         }
      }
      else if (sourceElement instanceof NonTerminalProgramElement) {
         NonTerminalProgramElement programElement = (NonTerminalProgramElement) sourceElement;
         for (int i = 0; i < programElement.getChildCount(); i++) {
            SourceElement childElement = programElement.getChildAt(i);
            if (childElement.toString().equals(fieldName)&& childElement instanceof FieldReference) {
               FieldReference field = (FieldReference) childElement;
               ProgramVariable progVar = field.getProgramVariable();
               if (fullFieldName.equals(progVar.toString())) {
                  return isAccess;
               }
            }
            else if (childElement instanceof NonTerminalProgramElement) {
               found = found || checkChildrenOfSourceElement(childElement);
            }
         }
      }
      return found;
   }
   
   /**
    * Checks if the Hitcount is exceeded for the given {@link JavaLineBreakpoint}.
    * If the Hitcount is not exceeded the hitted counter is incremented, otherwise its set to 0.
    * 
    * @return true if the Hitcount is exceeded or the {@link JavaLineBreakpoint} has no Hitcount.
    */
   private boolean hitcountExceeded(Node node){
      if (!(hitCount == -1)) {
         if(!hittedNodes.containsKey(node.serialNr())){
            if (hitCount == hitted + 1) {
               hitted=0;
               hittedNodes.put(node.serialNr(), Boolean.TRUE);
               return true;
            }
            else {
               hittedNodes.put(node.serialNr(), Boolean.FALSE);
               hitted++;
            }
         }else {
            return hittedNodes.get(node.serialNr());
         }
      }
      else {
         return true;
      }
      return false;
   }

   /**
    * @return the current hitCount
    */
   public int getHitCount() {
      return hitCount;
   }

   /**
    * @param hitCount the new hitCount
    */
   public void setHitCount(int hitCount) {
      this.hitCount = hitCount;
   }


   /**
    * @return if the breakpoint is enabled
    */
   public boolean isEnabled() {
      return enabled;
   }

   /**
    * @param enabled the new enabled value
    */
   public void setEnabled(boolean enabled) {
      this.enabled = enabled;
   }

   /**
    * @return the isAccess
    */
   public boolean isAccess() {
      return isAccess;
   }

   /**
    * @param isAccess the isAccess to set
    */
   public void setAccess(boolean isAccess) {
      this.isAccess = isAccess;
   }

   /**
    * @return the isModification
    */
   public boolean isModification() {
      return isModification;
   }

   /**
    * @param isModification the isModification to set
    */
   public void setModification(boolean isModification) {
      this.isModification = isModification;
   }
}
