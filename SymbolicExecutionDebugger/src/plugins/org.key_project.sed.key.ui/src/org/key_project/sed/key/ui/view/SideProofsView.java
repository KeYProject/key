package org.key_project.sed.key.ui.view;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ILazyContentProvider;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyAdapter;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.part.ViewPart;
import org.key_project.key4eclipse.common.ui.util.StarterUtil;
import org.key_project.sed.key.ui.provider.SideProofStoreContentProvider;
import org.key_project.sed.key.ui.util.LogUtil;
import org.key_project.sed.ui.util.SEDImages;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.symbolic_execution.util.SideProofStore;
import de.uka.ilkd.key.symbolic_execution.util.SideProofStore.Entry;

/**
 * This {@link ViewPart} shows the {@link Entry}s of {@link SideProofStore#DEFAULT_INSTANCE}.
 * @author Martin Hentschel
 */
public class SideProofsView extends ViewPart {
   /**
    * The ID of this view.
    */
   public static final String VIEW_ID = "org.key_project.sed.key.ui.view.SideProofsView";
   
   /**
    * Shows the {@link Entry}s of {@link SideProofStore#DEFAULT_INSTANCE}.
    */
   private TableViewer viewer;
   
   /**
    * The {@link ILazyContentProvider} of {@link #viewer}.
    */
   private SideProofStoreContentProvider viewerContentProvier;

   /**
    * Context menu item of {@link #viewer} to open the selected {@link Entry}s.
    */
   private Action openAction;

   /**
    * Context menu item of {@link #viewer} to delete the selected {@link Entry}s.
    */
   private Action deleteAction;

   /**
    * Context menu item of {@link #viewer} to enable or disable {@link SideProofStore#DEFAULT_INSTANCE}.
    */
   private Action collectAction;
   
   /**
    * Listens for changes on {@link SideProofStore#DEFAULT_INSTANCE}.
    */
   private final PropertyChangeListener storeListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleStorePropertyChange(evt);
      }
   };
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createPartControl(Composite parent) {
      viewer = new TableViewer(parent, SWT.MULTI | SWT.VIRTUAL | SWT.V_SCROLL | SWT.H_SCROLL);
      viewer.setUseHashlookup(true);
      viewerContentProvier = new SideProofStoreContentProvider();
      viewer.setContentProvider(viewerContentProvier);
      viewer.setInput(SideProofStore.DEFAULT_INSTANCE);
      viewer.addDoubleClickListener(new IDoubleClickListener() {
         @Override
         public void doubleClick(DoubleClickEvent event) {
            handleDoubleClick(event);
         }
      });
      viewer.addSelectionChangedListener(new ISelectionChangedListener() {
         @Override
         public void selectionChanged(SelectionChangedEvent event) {
            handleSelectionChanged(event);
         }
      });
      viewer.getControl().addKeyListener(new KeyAdapter() {
         @Override
         public void keyPressed(KeyEvent e) {
            handleKeyPressed(e);
         }
      });
      MenuManager viewerMenuManager = new MenuManager();
      openAction = new Action("&Open") {
         @Override
         public void run() {
            openEntries();
         }
      };
      openAction.setEnabled(false);
      viewerMenuManager.add(openAction);
      deleteAction = new Action("&Delete", SEDImages.getImageDescriptor(SEDImages.ANNOTATION_DELETE)) {
         @Override
         public void run() {
            deleteEntries();
         }
      };
      viewerMenuManager.add(deleteAction);
      viewerMenuManager.add(new Separator());
      collectAction = new Action("&Collect Side Proofs") {
         @Override
         public void run() {
            changeSideProofStoreEnabledState();
         }
      };
      collectAction.setChecked(SideProofStore.DEFAULT_INSTANCE.isEnabled());
      viewerMenuManager.add(collectAction);
      deleteAction.setEnabled(false);
      viewer.getControl().setMenu(viewerMenuManager.createContextMenu(viewer.getControl()));
      SideProofStore.DEFAULT_INSTANCE.addPropertyChangeListener(SideProofStore.PROP_ENABLED, storeListener);
   }

   /**
    * When a key was pressed on {@link #viewer}.
    * @param e The event.
    */
   protected void handleKeyPressed(KeyEvent e) {
      if (e.character == SWT.DEL) {
         deleteEntries();
      }
   }

   /**
    * A double click was performed on {@link #viewer}.
    * @param event The event.
    */
   protected void handleDoubleClick(DoubleClickEvent event) {
      openEntries();
   }

   /**
    * When the selection of {@link #viewer} has changed.
    * @param event The event.
    */
   protected void handleSelectionChanged(SelectionChangedEvent event) {
      boolean enabled = !event.getSelection().isEmpty();
      openAction.setEnabled(enabled);
      deleteAction.setEnabled(enabled);
   }
   
   /**
    * Opens all selected {@link Entry}s.
    */
   public void openEntries() {
      try {
         List<?> objects = SWTUtil.toList(viewer.getSelection());
         for (Object obj : objects) {
            if (obj instanceof Entry) {
               Entry entry = (Entry)obj;
               StarterUtil.openProofStarter(getSite().getShell(), 
                                            entry.getProof(), entry.getEnvironment(), 
                                            null, 
                                            true, 
                                            true, 
                                            true, 
                                            true);
            }
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getSite().getShell(), e);
      }
   }

   /**
    * Deletes all selected {@link Entry}s.
    */
   public void deleteEntries() {
      List<?> objects = SWTUtil.toList(viewer.getSelection());
      List<Entry> entries = new LinkedList<Entry>();
      for (Object obj : objects) {
         if (obj instanceof Entry) {
            entries.add((Entry)obj);
         }
      }
      if (!entries.isEmpty()) {
         SideProofStore.DEFAULT_INSTANCE.removeEntries(entries);
      }
   }

   /**
    * When {@link SideProofStore#isEnabled()} has changed.
    * @param evt The event.
    */
   protected void handleStorePropertyChange(PropertyChangeEvent evt) {
      collectAction.setChecked(SideProofStore.DEFAULT_INSTANCE.isEnabled());
   }

   /**
    * Updates the enabled state of {@link SideProofStore#DEFAULT_INSTANCE}.
    */
   protected void changeSideProofStoreEnabledState() {
      SideProofStore.DEFAULT_INSTANCE.setEnabled(collectAction.isChecked());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setFocus() {
      viewer.getControl().forceFocus();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      SideProofStore.DEFAULT_INSTANCE.removePropertyChangeListener(SideProofStore.PROP_ENABLED, storeListener);
      if (viewerContentProvier != null) {
         viewerContentProvier.dispose();
      }
      super.dispose();
   }
}
