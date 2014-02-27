package de.uka.ilkd.key.symbolic_execution.strategy;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * This{@link FieldWatchpointStopCondition} represents a Java watchpoint and is responsible to tell the debugger to stop execution when the respective
 * variable is accessed or modified.
 * 
 * @author Marco Drebing
 */
public class FieldWatchpointStopCondition extends
      HitCountBreakpointStopCondition {

   private boolean isAccess;

   private boolean isModification;

   private String fieldName;

   private String fullFieldName;
   
   private KeYJavaType containerKJT;


   /**
    * Creates a new {@link FieldWatchpointStopCondition}.
    * 
    * @param enabled flag if the Breakpoint is enabled
    * @param hitCount the number of hits after which the execution should hold at this breakpoint
    * @param fieldName the field to watch
    * @param isAcces flag to watch for accesses
    * @param isModification flag to watch for modifications
    * @param containerType the type of the element containing the breakpoint
    * @param proof the {@link Proof} that will be executed and should stop
    */
   public FieldWatchpointStopCondition(boolean enabled, int hitCount, String fieldName, boolean isAcces, boolean isModification, KeYJavaType containerKJT, Proof proof) {
      super(hitCount, proof, enabled);
      this.containerKJT=containerKJT;
      this.isAccess = isAcces;
      this.isModification = isModification;
      this.fieldName = "this."+fieldName;
      this.fullFieldName = containerKJT.getSort().toString()+"::"+fieldName;
   }
   
   /**
    * 
    */
   @Override
   protected boolean isBreakpointHit(SourceElement activeStatement,
         RuleApp ruleApp, Proof proof, Node node) throws ProofInputException {
      if (activeStatement != null && activeStatement instanceof Assignment) {
         Assignment assignment = (Assignment) activeStatement;
         SourceElement firstElement = assignment.getChildAt(0);
         SourceElement realFirstElement = assignment.getFirstElement();
         if(firstElement instanceof FieldReference){
            PosInOccurrence pio = ruleApp.posInOccurrence();
            Term term = pio.subTerm();
            getProof().getServices().getTermBuilder();
            term = TermBuilder.goBelowUpdates(term);
            ExecutionContext ec = JavaTools.getInnermostExecutionContext(term.javaBlock(), proof.getServices());
            ThisReference thisType = (ThisReference)realFirstElement;
            FieldReference fieldRef = (FieldReference)firstElement;
            KeYJavaType containerType = thisType.getKeYJavaType(proof.getServices(), ec);
            if(containerType!=null&&containerType.equals(containerKJT)&&fieldName.equals(fieldRef.toString())&&isModification&&hitcountExceeded(node)){
               return super.isBreakpointHit(activeStatement, ruleApp, proof, node);
            }
         }
         if(checkChildrenOfSourceElement(assignment)&&hitcountExceeded(node)){
            return super.isBreakpointHit(activeStatement, ruleApp, proof, node);
         }
      }else if (activeStatement != null) {
         if(checkChildrenOfSourceElement(activeStatement)&&hitcountExceeded(node)){
            return super.isBreakpointHit(activeStatement, ruleApp, proof, node);
         }
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
