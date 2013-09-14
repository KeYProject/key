package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.gui.ApplyStrategy.SingleRuleApplicationInfo;
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
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;

/**
 * This{@link JavaWatchpointNonSymbolicStopCondition} represents a Java watchpoint and is responsible to tell the debugger to stop execution when the respective
 * variable is accessed or modified.
 * 
 * @author Marco Drebing
 */
public class JavaWatchpointNonSymbolicStopCondition extends
      AbstractNonSymbolicHitCountBreakpointStopCondition {

   private boolean isAccess;

   private boolean isModification;

   private String fieldName;

   private String fullFieldName;
   
   private KeYJavaType containerKJT;


   /**
    * Creates a new {@link JavaWatchpointNonSymbolicStopCondition}.
    * 
    * @param enabled flag if the Breakpoint is enabled
    * @param hitCount the number of hits after which the execution should hold at this breakpoint
    * @param fieldName the field to watch
    * @param isAcces flag to watch for accesses
    * @param parentCondition a {@link CompoundStopCondition} containing this {@link LineBreakpointNonSymbolicStopCondition} and all other {@link LineBreakpointNonSymbolicStopCondition} the associated {@link Proof} should use
    * @param isModification flag to watch for modifications
    * @param containerType the type of the element containing the breakpoint
    * @param proof the {@link Proof} that will be executed and should stop
    */
   public JavaWatchpointNonSymbolicStopCondition(boolean enabled, int hitCount, String fieldName, boolean isAcces,
         CompoundStopCondition parentCondition, boolean isModification, KeYJavaType containerKJT, Proof proof) {
      super(hitCount, proof, parentCondition, enabled);
      this.containerKJT=containerKJT;
      this.isAccess = isAcces;
      this.isModification = isModification;
      this.fieldName = fieldName;
      this.fullFieldName = containerKJT.getSort().toString()+"::"+fieldName;
   }
   
   @Override
   public boolean shouldStop(int maxApplications, long timeout, Proof proof,
         IGoalChooser goalChooser, long startTime, int countApplied,
         SingleRuleApplicationInfo singleRuleApplicationInfo) {
      if (singleRuleApplicationInfo != null&&isEnabled()) {
         Goal goal = singleRuleApplicationInfo.getGoal();
         Node node = goal.node();
         RuleApp ruleApp = singleRuleApplicationInfo.getAppliedRuleApp();
         SourceElement activeStatement = NodeInfo.computeActiveStatement(ruleApp);
         if (activeStatement != null && activeStatement instanceof Assignment) {
            Assignment assignment = (Assignment) activeStatement;
            SourceElement firstElement = assignment.getFirstElement();
            if(firstElement instanceof LocationVariable){
               LocationVariable locVar = (LocationVariable)firstElement;
               KeYJavaType containerType = locVar.getContainerType();
               if(containerType!=null&&containerType.equals(containerKJT)&&fullFieldName.equals(locVar.toString())&&isModification&&hitcountExceeded(node)){
                  return true;
               }
            }
            if(checkChildrenOfSourceElement(assignment)&&hitcountExceeded(node)){
               return true;
            }
         }
//         else if (activeStatement != null) {
//            if(checkChildrenOfSourceElement(activeStatement)&&hitcountExceeded(node)){
//               return true;
//            }
//         }
      }
      return false;
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
