package de.uka.ilkd.key.symbolic_execution.slicing;

import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.Node;

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
                            Services services,
                            Set<Location> relevantLocations, 
                            SequentInfo info,
                            SourceElement activeStatement) {
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
      return accept;
   }
}
