package de.uka.ilkd.key.proof_references.analyst;

import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.ExpressionContainer;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.proof_references.reference.DefaultProofReference;
import de.uka.ilkd.key.proof_references.reference.IProofReference;

/**
 * Extracts read and write access to fields ({@link IProgramVariable}) via assignments.
 * @author Martin Hentschel
 */
public class ProgramVariableReferencesAnalyst implements IProofReferencesAnalyst {
   /**
    * {@inheritDoc}
    */
   @Override
   public LinkedHashSet<IProofReference<?>> computeReferences(Node node, Services services) {
      if (node.getAppliedRuleApp() != null && node.getNodeInfo() != null) {
         SourceElement statement = node.getNodeInfo().getActiveStatement();
         if (statement instanceof CopyAssignment) {
            LinkedHashSet<IProofReference<?>> result = new LinkedHashSet<IProofReference<?>>();
            listReferences(node, (CopyAssignment)statement, services.getJavaInfo().getArrayLength(), result, true);
            return result;
         }
         else if (statement instanceof If) {
            LinkedHashSet<IProofReference<?>> result = new LinkedHashSet<IProofReference<?>>();
            listReferences(node, ((If)statement).getExpression(), services.getJavaInfo().getArrayLength(), result, false);
            return result;
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }
   
   /**
    * Extracts the proof references recursive.
    * @param node The node.
    * @param pe The current {@link ProgramElement}.
    * @param arrayLength The {@link ProgramVariable} used for array length which is ignored.
    * @param toFill The {@link LinkedHashSet} to fill.
    * @param includeExpressionContainer Include {@link ExpressionContainer}?
    */
   protected void listReferences(Node node, ProgramElement pe, ProgramVariable arrayLength, LinkedHashSet<IProofReference<?>> toFill, boolean includeExpressionContainer) {
      if (pe instanceof ProgramVariable) {
         ProgramVariable pv = (ProgramVariable) pe;
         if (pv.isMember()) {
            DefaultProofReference<ProgramVariable> reference = new DefaultProofReference<ProgramVariable>(IProofReference.ACCESS, node, (ProgramVariable)pe);
            ProofReferenceUtil.merge(toFill, reference);
         }
      }
      else if (pe instanceof FieldReference) {
         FieldReference fr = (FieldReference) pe;
         ReferencePrefix ref = fr.getReferencePrefix();
         if (ref != null) {
            listReferences(node, ref, arrayLength, toFill, includeExpressionContainer);
         }
         ProgramVariable pv = fr.getProgramVariable();
         if (pv != arrayLength) {
            DefaultProofReference<ProgramVariable> reference = new DefaultProofReference<ProgramVariable>(IProofReference.ACCESS, node, pv);
            ProofReferenceUtil.merge(toFill, reference);
         }
      }
      else if (includeExpressionContainer && pe instanceof ExpressionContainer) {
         ExpressionContainer ec = (ExpressionContainer) pe;
         for (int i = ec.getChildCount() - 1; i >= 0; i--) {
             ProgramElement element = ec.getChildAt(i);
             listReferences(node, element, arrayLength, toFill, includeExpressionContainer);
         }
      }
   }
}
