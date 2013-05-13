package de.uka.ilkd.key.proof_references.reference;

import de.uka.ilkd.key.proof.Node;

/**
 * Default implementation of {@link IProofReference}.
 * @author Martin Hentschel
 */
public class DefaultProofReference<T> implements IProofReference<T> {
   /**
    * The reference kind as human readable {@link String}.
    */
   private String kind;

   /**
    * The target source member.
    */
   private T target;
   
   /**
    * The {@link Node} in which the reference was found.
    */
   private Node node;

   /**
    * Constructor
    * @param kind The reference kind as human readable {@link String}.
    * @param node The {@link Node} in which the reference was found.
    * @param target The target source member.
    */
   public DefaultProofReference(String kind, Node node, T target) {
      this.kind = kind;
      this.node = node;
      this.target = target;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public T getTarget() {
      return target;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Node getNode() {
      return node;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getKind() {
      return kind;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return getKind() + " Proof Reference to " + getTarget() + " of node" + getNode();
   }
}
