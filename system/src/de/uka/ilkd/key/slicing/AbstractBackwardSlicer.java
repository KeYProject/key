package de.uka.ilkd.key.slicing;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Node;

/**
 * Provides a basic implementation of backward slicing algorithms.
 * @author Martin Hentschel
 */
public abstract class AbstractBackwardSlicer extends AbstractSlicer {
   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableArray<Node> slice(Node seedNode, Expression seedLocation) {
      Set<Expression> relevantLocations = new HashSet<Expression>();
      relevantLocations.add(seedLocation);
      List<Node> result = new LinkedList<Node>();
      while (seedNode != null) {
         if (accept(seedNode, relevantLocations)) {
            result.add(seedNode);
         }
         seedNode = seedNode.parent();
      }
      return new ImmutableArray<Node>(result);
   }

   /**
    * Decides if the given {@link Node} is part of the slice or not.
    * @param node The {@link Node} to check.
    * @param relevantLocations The relevant locations.
    * @return {@code true} {@link Node} should be part of slice, {@code false} {@link Node} should not be part of slice.
    */
   protected abstract boolean accept(Node node, Set<Expression> relevantLocations);

   /**
    * Updates the relevant locations.
    * @param read The {@link Expression} which provides new relevant locations.
    * @param relevantLocations The relevant locations to update.
    * @param services The {@link Services} to use.
    */
   protected void updateRelevantLocations(final Expression read, 
                                          final Set<Expression> relevantLocations, 
                                          final Services services) {
      JavaASTVisitor visitor = new JavaASTVisitor(read, services) {
         @Override
         protected void doDefaultAction(SourceElement node) {
            if (node instanceof LocationVariable) {
               relevantLocations.add((LocationVariable) node);
            }
         }
      };
      visitor.start();
   }
}
