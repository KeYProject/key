package de.uka.ilkd.key.slicing;

import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.logic.Term;
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
   protected boolean accept(Node node, Set<Term> relevantLocations) {
      boolean accept = false;
      SourceElement activeStatement = node.getNodeInfo().getActiveStatement();
      if (activeStatement instanceof CopyAssignment) {
         CopyAssignment copyAssignment = (CopyAssignment) activeStatement;
         ImmutableArray<Expression> arguments = copyAssignment.getArguments();
         if (arguments.size() >= 1) {
            Services services = node.proof().getServices();
            Expression target = arguments.get(0);
            Term targetTerm = toTerm(services, target);
            if (relevantLocations.contains(targetTerm)) {
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
