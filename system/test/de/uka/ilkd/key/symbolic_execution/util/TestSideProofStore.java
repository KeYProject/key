package de.uka.ilkd.key.symbolic_execution.util;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import junit.framework.TestCase;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SideProofStore.Entry;
import de.uka.ilkd.key.symbolic_execution.util.event.ISideProofStoreListener;
import de.uka.ilkd.key.symbolic_execution.util.event.SideProofStoreEvent;
import de.uka.ilkd.key.ui.CustomUserInterface;
import de.uka.ilkd.key.util.Pair;

/**
 * Tests for {@link SideProofStore}
 * @author Martin Hentschel
 */
public class TestSideProofStore extends TestCase {
   /**
    * Tests the proof management and thrown events:
    * <ul>
    *    <li>{@link SideProofStore#containsEntry(Proof)}</li>
    *    <li>{@link SideProofStore#containsEntry(Entry)}</li>
    *    <li>{@link SideProofStore#getEntry(Proof)}</li>
    *    <li>{@link SideProofStore#countEntries()}</li>
    *    <li>{@link SideProofStore#getEntries()}</li>
    *    <li>{@link SideProofStore#getEntryAt(int)}</li>
    *    <li>{@link SideProofStore#addProof(String, Proof)}</li>
    *    <li>{@link SideProofStore#removeEntries(java.util.Collection)}</li>
    * </ul>
    */
   @SuppressWarnings("unchecked")
   public void testProofManagement() {
      LoggingProofStoreListener listener = new LoggingProofStoreListener();
      try {
         SideProofStore.DEFAULT_INSTANCE.addProofStoreListener(listener);
         // Create proofs
         Services services = new Services(AbstractProfile.getDefaultProfile());
         InitConfig ic = new InitConfig(services);
         ProofEnvironment pe = new ProofEnvironment(ic);
         Proof p1 = new Proof("TestSideProofStore 1", ic.deepCopy());
         p1.setEnv(pe);
         Proof p2 = new Proof("TestSideProofStore 2", ic.deepCopy());
         p2.setEnv(pe);
         Proof p3 = new Proof("TestSideProofStore 3", ic.deepCopy());
         p3.setEnv(pe);
         Proof[] allProofs = new Proof[] {p1, p2, p3};
         // Test initial state
         assertEntries(allProofs, new Proof[0]);
         // Add proof p1
         SideProofStore.DEFAULT_INSTANCE.addProof("P1", p1);
         assertEntries(allProofs, new Proof[0], new Pair<String, Proof>("P1", p1));
         listener.assertAddedLog(new SideProofStoreEvent(SideProofStore.DEFAULT_INSTANCE, new Entry[] {SideProofStore.DEFAULT_INSTANCE.getEntry(p1)}));
         listener.assertRemovedLog();
         // Add proof p2
         SideProofStore.DEFAULT_INSTANCE.addProof("P2", p2);
         assertEntries(allProofs, new Proof[0], new Pair<String, Proof>("P1", p1), new Pair<String, Proof>("P2", p2));
         listener.assertAddedLog(new SideProofStoreEvent(SideProofStore.DEFAULT_INSTANCE, new Entry[] {SideProofStore.DEFAULT_INSTANCE.getEntry(p2)}));
         listener.assertRemovedLog();
         // Add proof p3
         SideProofStore.DEFAULT_INSTANCE.addProof("P3", p3);
         assertEntries(allProofs, new Proof[0], new Pair<String, Proof>("P1", p1), new Pair<String, Proof>("P2", p2), new Pair<String, Proof>("P3", p3));
         listener.assertAddedLog(new SideProofStoreEvent(SideProofStore.DEFAULT_INSTANCE, new Entry[] {SideProofStore.DEFAULT_INSTANCE.getEntry(p3)}));
         listener.assertRemovedLog();
         // Remove p1 and p3
         List<Entry> toRemove = new LinkedList<Entry>();
         toRemove.add(SideProofStore.DEFAULT_INSTANCE.getEntry(p1));
         toRemove.add(SideProofStore.DEFAULT_INSTANCE.getEntry(p3));
         SideProofStore.DEFAULT_INSTANCE.removeEntries(toRemove);
         assertEntries(allProofs, new Proof[] {p1, p3}, new Pair<String, Proof>("P2", p2));
         listener.assertAddedLog();
         listener.assertRemovedLog(new SideProofStoreEvent(SideProofStore.DEFAULT_INSTANCE, toRemove.toArray(new Entry[toRemove.size()])));
         // Remove p2
         toRemove = Collections.singletonList(SideProofStore.DEFAULT_INSTANCE.getEntry(p2));
         SideProofStore.DEFAULT_INSTANCE.removeEntries(toRemove);
         assertEntries(allProofs, new Proof[] {p1, p2, p3});
         listener.assertAddedLog();
         listener.assertRemovedLog(new SideProofStoreEvent(SideProofStore.DEFAULT_INSTANCE, toRemove.toArray(new Entry[toRemove.size()])));
      }
      finally {
         SideProofStore.DEFAULT_INSTANCE.removeProofStoreListener(listener);
      }
   }
   
   /**
    * Ensures the {@link Entry} is {@link SideProofStore#DEFAULT_INSTANCE}.
    * @param allProofs All available {@link Proof}s.
    * @param disposedProofs The expected disposed {@link Proof}s.
    * @param expectedEntries The expected entries in {@link SideProofStore#DEFAULT_INSTANCE}.
    */
   private void assertEntries(Proof[] allProofs, Proof[] disposedProofs, Pair<String, Proof>... expectedEntries) {
      // Test entries
      List<Proof> containedProofs = new LinkedList<Proof>();
      assertEquals(expectedEntries.length, SideProofStore.DEFAULT_INSTANCE.countEntries());
      Entry[] entries = SideProofStore.DEFAULT_INSTANCE.getEntries();
      assertEquals(expectedEntries.length, entries.length);
      for (int i = 0; i < expectedEntries.length; i++) {
         assertEquals(entries[i].getDescription(), expectedEntries[i].first);
         assertSame(entries[i].getProof(), expectedEntries[i].second);
         assertSame(entries[i], SideProofStore.DEFAULT_INSTANCE.getEntryAt(i));
         KeYEnvironment<CustomUserInterface> ui = entries[i].getEnvironment();
         assertNotNull(ui);
         KeYEnvironment<CustomUserInterface> uiAgain = entries[i].getEnvironment();
         assertSame(ui, uiAgain);
         containedProofs.add(expectedEntries[i].second);
         assertFalse(entries[i].getProof().isDisposed());
         Object[] user = ProofUserManager.getInstance().getUsers(entries[i].getProof());
         assertEquals(1, user.length);
         assertSame(SideProofStore.DEFAULT_INSTANCE, user[0]);
      }
      // Test proofs
      for (Proof proof : allProofs) {
         Entry entry = SideProofStore.DEFAULT_INSTANCE.getEntry(proof);
         assertEquals(containedProofs.contains(proof), entry != null);
         assertEquals(containedProofs.contains(proof), SideProofStore.DEFAULT_INSTANCE.containsEntry(proof));
         assertEquals(containedProofs.contains(proof), SideProofStore.DEFAULT_INSTANCE.containsEntry(entry));
         assertEquals(JavaUtil.contains(disposedProofs, proof), proof.isDisposed());
      }
   }

   /**
    * A logging {@link ISideProofStoreListener}.
    * @author Martin Hentschel
    */
   private static class LoggingProofStoreListener implements ISideProofStoreListener {
      /**
       * The log with added entries.
       */
      private final List<SideProofStoreEvent> addedLog = new LinkedList<SideProofStoreEvent>();
      
      /**
       * The log with removed entries.
       */
      private final List<SideProofStoreEvent> removedLog = new LinkedList<SideProofStoreEvent>();

      /**
       * {@inheritDoc}
       */
      @Override
      public void entriesAdded(SideProofStoreEvent e) {
         addedLog.add(e);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void entriesRemoved(SideProofStoreEvent e) {
         removedLog.add(e);
      }
      
      /**
       * Compares the log with the given events and clears the log.
       * @param expectedEvents The expected {@link SideProofStoreEvent}s.
       */
      public void assertAddedLog(SideProofStoreEvent... expectedEvents) {
         assertLog(addedLog, expectedEvents);
      }
      
      /**
       * Compares the log with the given events and clears the log.
       * @param expectedEvents The expected {@link SideProofStoreEvent}s.
       */
      public void assertRemovedLog(SideProofStoreEvent... expectedEvents) {
         assertLog(removedLog, expectedEvents);
      }
      
      /**
       * Compares the log with the given events and clears the log.
       * @param log The logged events.
       * @param expectedEvents The expected {@link SideProofStoreEvent}s.
       */
      protected void assertLog(List<SideProofStoreEvent> log, SideProofStoreEvent... expectedEvents) {
         assertEquals(expectedEvents.length, log.size());
         for (int i = 0; i < log.size(); i++) {
            SideProofStoreEvent currentLog = log.get(i);
            assertEquals(expectedEvents[i].getSource(), currentLog.getSource());
            assertEquals(expectedEvents[i].getEntries().length, currentLog.getEntries().length);
            for (int j = 0; j < expectedEvents[i].getEntries().length; j++) {
               assertEquals(expectedEvents[i].getEntries()[j], currentLog.getEntries()[j]);
            }
         }
         log.clear();
      }
   }
   
   /**
    * Tests {@link SideProofStore#isEnabled()} and 
    * {@link SideProofStore#setEnabled(boolean)} together with the thrown events
    * and the event management.
    */
   public void testEnabledState() {
      LoggingPropertyChangeListener listener = new LoggingPropertyChangeListener();
      boolean originalEnabled = SideProofStore.DEFAULT_INSTANCE.isEnabled();
      try {
         // Setup initial disabled state
         SideProofStore.DEFAULT_INSTANCE.setEnabled(false);
         SideProofStore.DEFAULT_INSTANCE.addPropertyChangeListener(SideProofStore.PROP_ENABLED, listener);
         // Test initial disabled state
         assertFalse(SideProofStore.DEFAULT_INSTANCE.isEnabled());
         listener.assertLog();
         // Set disabled again
         SideProofStore.DEFAULT_INSTANCE.setEnabled(false);
         assertFalse(SideProofStore.DEFAULT_INSTANCE.isEnabled());
         listener.assertLog();
         // Change to enabled
         SideProofStore.DEFAULT_INSTANCE.setEnabled(true);
         assertTrue(SideProofStore.DEFAULT_INSTANCE.isEnabled());
         listener.assertLog(new PropertyChangeEvent(SideProofStore.DEFAULT_INSTANCE, SideProofStore.PROP_ENABLED, false, true));
         // Set enabled again
         SideProofStore.DEFAULT_INSTANCE.setEnabled(true);
         assertTrue(SideProofStore.DEFAULT_INSTANCE.isEnabled());
         listener.assertLog();
         // Change to dissabled
         SideProofStore.DEFAULT_INSTANCE.setEnabled(false);
         assertFalse(SideProofStore.DEFAULT_INSTANCE.isEnabled());
         listener.assertLog(new PropertyChangeEvent(SideProofStore.DEFAULT_INSTANCE, SideProofStore.PROP_ENABLED, true, false));
      }
      finally {
         SideProofStore.DEFAULT_INSTANCE.removePropertyChangeListener(SideProofStore.PROP_ENABLED, listener);
         SideProofStore.DEFAULT_INSTANCE.setEnabled(originalEnabled);
      }
   }
   
   /**
    * A logging {@link PropertyChangeListener}.
    * @author Martin Hentschel
    */
   private static class LoggingPropertyChangeListener implements PropertyChangeListener {
      /**
       * The log.
       */
      private final List<PropertyChangeEvent> log = new LinkedList<PropertyChangeEvent>();

      /**
       * {@inheritDoc}
       */
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         log.add(evt);
      }

      /**
       * Compares the log with the given events and clears the log.
       * @param expectedEvents The expected {@link PropertyChangeEvent}s.
       */
      public void assertLog(PropertyChangeEvent... expectedEvents) {
         assertEquals(expectedEvents.length, log.size());
         for (int i = 0; i < log.size(); i++) {
            PropertyChangeEvent currentLog = log.get(i);
            assertEquals(expectedEvents[i].getSource(), currentLog.getSource());
            assertEquals(expectedEvents[i].getPropertyName(), currentLog.getPropertyName());
            assertEquals(expectedEvents[i].getOldValue(), currentLog.getOldValue());
            assertEquals(expectedEvents[i].getNewValue(), currentLog.getNewValue());
         }
         log.clear();
      }
   }
}
