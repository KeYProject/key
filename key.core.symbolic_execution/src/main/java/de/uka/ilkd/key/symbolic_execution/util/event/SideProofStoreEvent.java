package de.uka.ilkd.key.symbolic_execution.util.event;

import java.util.EventObject;

import de.uka.ilkd.key.symbolic_execution.util.SideProofStore;
import de.uka.ilkd.key.symbolic_execution.util.SideProofStore.Entry;

/**
 * An event thrown by a {@link SideProofStore} and observed via an {@link ISideProofStoreListener}.
 * @author Martin Hentschel
 */
public class SideProofStoreEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = 8046460017292232070L;

   /**
    * The added or removed {@link Entry}s.
    */
   private final Entry[] entries;
   
   /**
    * Constructor.
    * @param source The source.
    * @param proof The added or removed {@link Entry}s.
    */
   public SideProofStoreEvent(SideProofStore source, Entry[] entries) {
      super(source);
      this.entries = entries;
   }

   /**
    * Returns the added or removed {@link Entry}s.
    * @return The added or removed {@link Entry}s.
    */
   public Entry[] getEntries() {
      return entries;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public SideProofStore getSource() {
      return (SideProofStore)super.getSource();
   }
}
