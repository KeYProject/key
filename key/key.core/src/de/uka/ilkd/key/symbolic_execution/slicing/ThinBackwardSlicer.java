package de.uka.ilkd.key.symbolic_execution.slicing;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Implementation of thin backward slicing.
 * @author Martin Hentschel
 */
public class ThinBackwardSlicer extends AbstractBackwardSlicer {
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean accept(Node node, 
                            Node previousChild,
                            Services services,
                            Set<Location> relevantLocations, 
                            SequentInfo info,
                            SourceElement activeStatement) {
      try {
         boolean accept = false;
         if (activeStatement instanceof CopyAssignment) {
            CopyAssignment copyAssignment = (CopyAssignment) activeStatement;
            ImmutableArray<Expression> arguments = copyAssignment.getArguments();
            if (arguments.size() >= 1) {
               SourceElement originalTarget = arguments.get(0);
               ReferencePrefix relevantTarget = toReferencePrefix(originalTarget);
               if (relevantTarget != null && removeRelevant(services, relevantTarget, relevantLocations, info)) {
                  accept = true;
                  for (int i = 1; i < arguments.size(); i++) {
                     Expression read = arguments.get(i);
                     updateRelevantLocations(read, relevantLocations, info, services);
                  }
               }
            }
         }
         else if (activeStatement instanceof MethodBodyStatement) {
            MethodBodyStatement mbs = (MethodBodyStatement) activeStatement;
            IProgramVariable resultVariable = mbs.getResultVariable();
            ReferencePrefix relevantTarget = toReferencePrefix(resultVariable);
            if (relevantTarget != null && removeRelevant(services, relevantTarget, relevantLocations, info)) {
               accept = true;            
            }
         }
         else if (SymbolicExecutionUtil.isLoopInvariant(node, node.getAppliedRuleApp())) {
            // Compute this reference
            PosInOccurrence pio = node.getAppliedRuleApp().posInOccurrence();
            // Compute modified locations
            List<Location> modifiedLocations = new LinkedList<Location>();
            Term loopConditionModalityTerm = SymbolicExecutionUtil.posInOccurrenceInOtherNode(node, pio, previousChild);
            if (loopConditionModalityTerm.op() != UpdateApplication.UPDATE_APPLICATION) {
               throw new IllegalStateException("Use Loop Invariant rule implementation has changed.");
            }
            Term updateTerm = UpdateApplication.getTarget(loopConditionModalityTerm);
            while (updateTerm.op() == UpdateApplication.UPDATE_APPLICATION) {
               listModifiedLocations(UpdateApplication.getUpdate(updateTerm), services, services.getTypeConverter().getHeapLDT(), modifiedLocations, info.getExecutionContext(), info.getThisReference());
               updateTerm = UpdateApplication.getTarget(updateTerm);
            }
            // Check modified locations
            for (Location location : modifiedLocations) {
               if (removeRelevant(services, location, relevantLocations, info)) {
                  accept = true;            
               }
            }
         }
         else if (SymbolicExecutionUtil.isOperationContract(node, node.getAppliedRuleApp())) {
            // TODO: Implement support for operation contracts
         }
         return accept;
      }
      catch (IllegalArgumentException e) {
         return false; // Do not accept, expression with side effects is evaluated
      }
   }
}
