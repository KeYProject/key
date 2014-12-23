package de.uka.ilkd.key.symbolic_execution.util;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.symbolic_execution.util.event.ISideProofStoreListener;
import de.uka.ilkd.key.symbolic_execution.util.event.SideProofStoreEvent;
import de.uka.ilkd.key.ui.CustomUserInterface;

/**
 * <p>
 * The only instance of this class {@link #DEFAULT_INSTANCE} is used
 * to manage performed side proofs.
 * </p>
 * <p>
 * Side proofs are added via {@link #disposeOrStore(String, ApplyStrategyInfo)}
 * when they are no longer needed. If the {@link SideProofStore} is enabled ({@link #isEnabled()})
 * the side {@link Proof} is not disposed; instead it is added via {@link #addProof(String, Proof)}
 * and available for a later access until it is removed via {@link #removeEntries(Collection)}.
 * </p>
 * @author Martin Hentschel
 */
public final class SideProofStore {
   /**
    * Property {@link #isEnabled()}.
    */
   public static final String PROP_ENABLED = "enabled";
   
   /**
    * The default and only instance of this class.
    */
   public static final SideProofStore DEFAULT_INSTANCE = new SideProofStore();
   
   /**
    * All contained {@link Entry}s.
    */
   private final List<Entry> entries = new LinkedList<Entry>();
   
   /**
    * All available {@link ISideProofStoreListener}.
    */
   private final List<ISideProofStoreListener> listener = new LinkedList<ISideProofStoreListener>();
   
   /**
    * The enabled state.
    */
   private boolean enabled = false;
   
   /**
    * The {@link PropertyChangeSupport}.
    */
   private PropertyChangeSupport pcs = new PropertyChangeSupport(this);

   /**
    * Forbid other instances.
    */
   private SideProofStore() {
   }
   
   /**
    * Checks if the {@link SideProofStore} is enabled or not.
    * @return {@code true} enabled, {@code false} disabled.
    */
   public boolean isEnabled() {
      return enabled;
   }

   /**
    * Defines the enabled state.
    * @param enabled {@code true} enabled, {@code false} disabled.
    */
   public void setEnabled(boolean enabled) {
      boolean oldValue = isEnabled();
      this.enabled = enabled;
      pcs.firePropertyChange(PROP_ENABLED, oldValue, isEnabled());
   }

   /**
    * Adds a new {@link Proof}.
    * @param description The description.
    * @param proof The {@link Proof} to add.
    */
   public void addProof(String description, Proof proof) {
      synchronized (entries) {
         if (!containsEntry(proof)) {
            Entry entry = new Entry(description, proof);
            ProofUserManager.getInstance().addUser(entry.getProof(), entry.getEnvironment(), this);
            entries.add(entry);
            fireEntriesAdded(new SideProofStoreEvent(this, new Entry[] {entry}));
         }
      }
   }
   
   /**
    * Removes the given {@link Entry}s.
    * @param entries The {@link Entry}s to remove.
    */
   public void removeEntries(Collection<Entry> entries) {
      synchronized (entries) {
         if (this.entries.removeAll(entries)) {
            for (Entry entry : entries) {
               ProofUserManager.getInstance().removeUserAndDispose(entry.getProof(), this);
            }
            fireEntriesRemoved(new SideProofStoreEvent(this, entries.toArray(new Entry[entries.size()])));
         }
      }
   }

   /**
    * Removes all {@link Entry}s.
    */
   public void clearProofs() {
      removeEntries(new LinkedList<Entry>(entries));
   }
   
   /**
    * Checks if an {@link Entry} for the given {@link Proof} exist.
    * @param proof The {@link Proof} to check.
    * @return {@code true} {@link Entry} for {@link Proof} exist, {@code false} otherwise.
    */
   public boolean containsEntry(Proof proof) {
      return getEntry(proof) != null;
   }
   
   /**
    * Returns the {@link Entry} for the given {@link Proof}.
    * @param proof The {@link Proof} for which the {@link Entry} is requested.
    * @return The {@link Entry} with the given {@link Proof} or {@code null} if not available.
    */
   public Entry getEntry(final Proof proof) {
      return JavaUtil.search(entries, new IFilter<Entry>() {
         @Override
         public boolean select(Entry element) {
            return element != null && element.getProof() == proof;
         }
      });
   }

   /**
    * Checks if the given {@link Entry} is contained.
    * @param entry The {@link Entry} to check.
    * @return {@code true} {@link Entry} is contained, {@code false} {@link Entry} is not contained.
    */
   public boolean containsEntry(Entry entry) {
      return entries.contains(entry);
   }
   
   /**
    * Returns the number of contained {@link Entry}s.
    * @return The number of contained {@link Entry}s.
    */
   public int countEntries() {
      return entries.size();
   }

   /**
    * Returns the {@link Entry} at the given index.
    * @param index The index.
    * @return The {@link Entry} at the given index.
    */
   public Entry getEntryAt(int index) {
      return index >= 0 && index < entries.size() ? 
             entries.get(index) :
             null;
   }
   
   /**
    * Returns all available {@link Entry}s.
    * @return All available {@link Entry}s.
    */
   public Entry[] getEntries() {
      return entries.toArray(new Entry[entries.size()]);
   }
   
   /**
    * Registers the {@link ISideProofStoreListener}.
    * @param l The {@link ISideProofStoreListener} to register.
    */
   public void addProofStoreListener(ISideProofStoreListener l) {
      if (l != null) {
         listener.add(l);
      }
   }
   
   /**
    * Unregisters the {@link ISideProofStoreListener}.
    * @param l The {@link ISideProofStoreListener} to unregister.
    */
   public void removeProofStoreListener(ISideProofStoreListener l) {
      if (l != null) {
         listener.remove(l);
      }
   }
   
   /**
    * Returns all registered {@link ISideProofStoreListener}.
    * @return All registered {@link ISideProofStoreListener}.
    */
   public ISideProofStoreListener[] getProofStoreListener() {
      return listener.toArray(new ISideProofStoreListener[listener.size()]);
   }
   
   /**
    * Fires the event {@link ISideProofStoreListener#entriesAdded(SideProofStoreEvent)}.
    * @param e The event.
    */
   protected void fireEntriesAdded(SideProofStoreEvent e) {
      ISideProofStoreListener[] listener = getProofStoreListener();
      for (ISideProofStoreListener l : listener) {
         l.entriesAdded(e);
      }
   }
   
   /**
    * Fires the event {@link ISideProofStoreListener#entriesRemoved(SideProofStoreEvent)}.
    * @param e The event.
    */
   protected void fireEntriesRemoved(SideProofStoreEvent e) {
      ISideProofStoreListener[] listener = getProofStoreListener();
      for (ISideProofStoreListener l : listener) {
         l.entriesRemoved(e);
      }
   }
   
   /**
    * Adds the given listener.
    * @param listener The listener to add.
    */
   public void addPropertyChangeListener(PropertyChangeListener listener) {
       pcs.addPropertyChangeListener(listener);
   }
   
   /**
    * Adds the given listener for the given property only.
    * @param propertyName The property to observe.
    * @param listener The listener to add.
    */
   public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
       pcs.addPropertyChangeListener(propertyName, listener);
   }
   
   /**
    * Removes the given listener.
    * @param listener The listener to remove.
    */
   public void removePropertyChangeListener(PropertyChangeListener listener) {
       pcs.removePropertyChangeListener(listener);
   }
   
   /**
    * Removes the given listener from the given property.
    * @param propertyName The property to no longer observe.
    * @param listener The listener to remove.
    */
   public void removePropertyChangeListener(String propertyName, PropertyChangeListener listener) {
       pcs.removePropertyChangeListener(propertyName, listener);
   }
   
   /**
    * An {@link Entry} of a {@link SideProofStore}.
    * @author Martin Hentschel
    */
   public static class Entry {
      /**
       * The description.
       */
      private final String description;
      
      /**
       * The {@link Proof}.
       */
      private final Proof proof;
      
      /**
       * The {@link KeYEnvironment}.
       */
      private final KeYEnvironment<CustomUserInterface> environment;

      /**
       * Constructor.
       * @param description The description.
       * @param proof The {@link Proof}.
       */
      public Entry(String description, Proof proof) {
         this.description = description;
         this.proof = proof;
         CustomUserInterface ui = new CustomUserInterface(false);
         this.environment = new KeYEnvironment<CustomUserInterface>(ui, proof.getInitConfig(), proof);
      }

      /**
       * Returns the description.
       * @return The description.
       */
      public String getDescription() {
         return description;
      }

      /**
       * Returns the {@link Proof}.
       * @return The {@link Proof}.
       */
      public Proof getProof() {
         return proof;
      }

      /**
       * Returns the {@link KeYEnvironment}.
       * @return The {@link KeYEnvironment}.
       */
      public KeYEnvironment<CustomUserInterface> getEnvironment() {
         return environment;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String toString() {
         return description;
      }
   }
}
