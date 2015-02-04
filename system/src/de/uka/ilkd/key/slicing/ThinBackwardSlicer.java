package de.uka.ilkd.key.slicing;

import java.util.Map;
import java.util.Set;
import java.util.SortedSet;

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
                            Map<ReferencePrefix, SortedSet<ReferencePrefix>> aliases,
                            ReferencePrefix thisReference,
                            SourceElement activeStatement) {
      boolean accept = false;
      if (activeStatement instanceof CopyAssignment) {
         CopyAssignment copyAssignment = (CopyAssignment) activeStatement;
         ImmutableArray<Expression> arguments = copyAssignment.getArguments();
         if (arguments.size() >= 1) {
            Services services = node.proof().getServices();
            SourceElement originalTarget = arguments.get(0);
            ReferencePrefix relevantTarget = computeReferencePrefix(originalTarget);
            if (relevantTarget != null && removeRelevant(relevantTarget, relevantLocations, aliases, thisReference)) {
               accept = true;
               for (int i = 1; i < arguments.size(); i++) {
                  Expression read = arguments.get(i);
                  updateRelevantLocations(read, relevantLocations, aliases, thisReference, services);
               }
            }
         }
      }
      return accept;
   }
}
