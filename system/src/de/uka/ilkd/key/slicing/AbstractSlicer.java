package de.uka.ilkd.key.slicing;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;

/**
 * Defines the basic functionality for slicing algorithms.
 * @author Martin Hentschel
 */
public abstract class AbstractSlicer {
   /**
    * Computes the slice.
    * @param seedNode The seed {@link Node} to start slicing at.
    * @param seedLocation The seed {@link Term}.
    * @return The computed slice.
    */
   public ImmutableArray<Node> slice(Node seedNode, Term seedLocation) {
      if (seedLocation.op() instanceof Expression) {
         return slice(seedNode, (Expression) seedLocation.op());
      }
      else {
         throw new IllegalStateException("Seed location '" + seedLocation + "' not supported.");
      }
   }
   
   /**
    * Computes the slice.
    * @param seedNode The seed {@link Node} to start slicing at.
    * @param seedLocation The seed {@link Expression}.
    * @return The computed slice.
    */
   public abstract ImmutableArray<Node> slice(Node seedNode, Expression seedLocation);
}
