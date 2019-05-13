package de.uka.ilkd.key.proof.event;

import java.util.EventObject;

import de.uka.ilkd.key.proof.Proof;

/**
 * An event thrown by a {@link Proof} and observed via a {@link ProofDisposedListener}.
 * @author Martin Hentschel
 */
public class ProofDisposedEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = -1584989528889751997L;

   /**
    * Constructor.
    * @param source The {@link Proof}.
    */
   public ProofDisposedEvent(Proof source) {
      super(source);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Proof getSource() {
      return (Proof)super.getSource();
   }
}
