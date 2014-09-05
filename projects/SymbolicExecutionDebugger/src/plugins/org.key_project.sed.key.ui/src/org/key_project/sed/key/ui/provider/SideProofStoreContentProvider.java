package org.key_project.sed.key.ui.provider;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.viewers.AbstractTableViewer;
import org.eclipse.jface.viewers.ILazyContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.SideProofStore;
import de.uka.ilkd.key.symbolic_execution.util.SideProofStore.Entry;
import de.uka.ilkd.key.symbolic_execution.util.event.ISideProofStoreListener;
import de.uka.ilkd.key.symbolic_execution.util.event.SideProofStoreEvent;

/**
 * An {@link ILazyContentProvider} which shows the {@link Entry}s of a {@link SideProofStore}.
 * @author Martin Hentschel
 */
public class SideProofStoreContentProvider implements ILazyContentProvider {
   /**
    * The {@link AbstractTableViewer} in which this {@link ILazyContentProvider} is used.
    */
   private AbstractTableViewer viewer;

   /**
    * The {@link SideProofStore} for which {@link Entry}s are shown.
    */
   private SideProofStore store;
   
   /**
    * Listens for changes on {@link #store}.
    */
   private final ISideProofStoreListener storeListener = new ISideProofStoreListener() {
      @Override
      public void entriesAdded(SideProofStoreEvent e) {
         handleProofAdded(e);
      }

      @Override
      public void entriesRemoved(SideProofStoreEvent e) {
         handleProofRemoved(e);
      }
   };
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
      Assert.isTrue(viewer instanceof AbstractTableViewer);
      if (store != null) {
         store.removeProofStoreListener(storeListener);
      }
      this.viewer = (AbstractTableViewer)viewer;
      if (newInput instanceof SideProofStore) {
         store = (SideProofStore)newInput;
         store.addProofStoreListener(storeListener);
         this.viewer.setItemCount(store.countEntries());
      }
      else {
         this.viewer.setItemCount(0);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void updateElement(int index) {
      Entry entry = store.getEntryAt(index);
      if (entry != null) {
         viewer.replace(entry, index);
      }
   }

   /**
    * When a {@link Proof} was added.
    * @param e The event.
    */
   protected void handleProofAdded(SideProofStoreEvent e) {
      SWTUtil.addAsync(viewer, e.getEntries()); // Has to be asynchronous because side proofs might be performed in the UI thread which can cause dead locks with synchronous invocation.
   }

   /**
    * When a {@link Proof} was removed.
    * @param e The event.
    */
   protected void handleProofRemoved(SideProofStoreEvent e) {
      SWTUtil.remove(viewer, e.getEntries());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (store != null) {
         store.removeProofStoreListener(storeListener);
      }
   }
}
