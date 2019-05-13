package de.uka.ilkd.key.symbolic_execution.util.event;

import java.util.EventListener;

import de.uka.ilkd.key.symbolic_execution.util.SideProofStore;
import de.uka.ilkd.key.symbolic_execution.util.SideProofStore.Entry;

/**
 * Observes changes on a {@link SideProofStore}.
 * @author Martin Hentschel
 */
public interface ISideProofStoreListener extends EventListener {
   /**
    * When new {@link Entry}s are added.
    * @param e The {@link SideProofStoreEvent}.
    */
   public void entriesAdded(SideProofStoreEvent e);
   
   /**
    * When existing {@link Entry}s were removed.
    * @param e The {@link SideProofStoreEvent}.
    */
   public void entriesRemoved(SideProofStoreEvent e);
}
