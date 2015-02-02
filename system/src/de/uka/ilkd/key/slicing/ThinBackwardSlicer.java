package de.uka.ilkd.key.slicing;

import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
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
                            Set<ReferencePrefix> relevantLocations, 
                            Map<ReferencePrefix, Set<ReferencePrefix>> aliases) {
      boolean accept = false;
      SourceElement activeStatement = node.getNodeInfo().getActiveStatement();
      if (activeStatement instanceof CopyAssignment) {
         CopyAssignment copyAssignment = (CopyAssignment) activeStatement;
         ImmutableArray<Expression> arguments = copyAssignment.getArguments();
         if (arguments.size() >= 1) {
            Services services = node.proof().getServices();
            SourceElement originalTarget = arguments.get(0);
            ReferencePrefix relevantTarget = computeReferencePrefix(originalTarget);
            if (relevantTarget != null && isRelevant(relevantTarget, relevantLocations, aliases)) {
               accept = true;
               for (int i = 1; i < arguments.size(); i++) {
                  Expression read = arguments.get(i);
                  updateRelevantLocations(read, relevantLocations, services);
               }
            }
         }
      }
      return accept;
   }
}
