/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package de.hentschel.visualdbc.statistic.ui.util;

import org.eclipse.core.runtime.Assert;
import org.eclipse.emf.edit.provider.ComposedAdapterFactory;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ocl.util.ObjectUtil;
import org.eclipse.swt.events.TreeAdapter;
import org.eclipse.swt.events.TreeEvent;
import org.eclipse.swt.events.TreeListener;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.services.IDisposable;

import de.hentschel.visualdbc.dbcmodel.DbcProof;

/**
 * Provides a basic functionality to modify the shown {@link TreeItem}s
 * in a {@link TreeViewer} that uses providers based on a {@link ComposedAdapterFactory}.
 * @author Martin Hentschel
 */
public abstract class AbstractTreeItemDecorator implements IDisposable {
   /**
    * The observed {@link TreeViewer}.
    */
   private TreeViewer viewer;
   
   /**
    * Listens for changes on {@link #viewer}.
    */
   private TreeListener treeListener = new TreeAdapter() {
      @Override
      public void treeExpanded(TreeEvent e) {
         handleTreeExpanded(e);
      }
   };
   
   /**
    * Listens for changes on an {@link ILabelProvider}.
    */
   private ILabelProviderListener labelProviderListener = new ILabelProviderListener() {
      @Override
      public void labelProviderChanged(LabelProviderChangedEvent event) {
         handleLabelProviderChanged(event);
      }
   };

   /**
    * Constructor.
    * @param viewer The observed {@link TreeViewer}.
    */
   public AbstractTreeItemDecorator(TreeViewer viewer) {
      super();
      Assert.isNotNull(viewer);
      this.viewer = viewer;
      viewer.getTree().addTreeListener(treeListener);
      if (viewer.getLabelProvider() != null) {
         viewer.getLabelProvider().addListener(labelProviderListener);
      }
   }

   /**
    * Updates all {@link TreeItem}s in the viewer.
    */
   public void initTreeItems() {
      if (!viewer.getTree().isDisposed()) {
         TreeItem[] items = viewer.getTree().getItems();
         updateTreeItems(items);
      }
   }

   /**
    * Updates recursive all {@link TreeItem}s.
    * @param items The given {@link TreeItem}s to update.
    */
   protected void updateTreeItems(TreeItem[] items) {
      if (items != null) {
         for (TreeItem item : items) {
            updateTreeItem(item);
            TreeItem[] childItems = item.getItems();
            updateTreeItems(childItems);
         }
      }
   }
   
   /**
    * Updates the {@link TreeItem}.
    * @param item The {@link TreeItem} to update.
    */
   protected abstract void updateTreeItem(TreeItem item);

   /**
    * When a {@link TreeItem} was expanded.
    * @param e The event.
    */
   protected void handleTreeExpanded(TreeEvent e) {
      if (e.item instanceof TreeItem) {
         TreeItem item = (TreeItem)e.item;
         updateTreeItems(item.getItems());
      }
   }

   /**
    * When the {@link ILabelProvider} updates a row.
    * @param event The event.
    */
   protected void handleLabelProviderChanged(final LabelProviderChangedEvent event) {
      // Update TreeItem asynchronous because the event is caught before the cell content is updated.
      viewer.getTree().getDisplay().asyncExec(new Runnable() {
         @Override
         public void run() {
            for (Object element : event.getElements()) {
               if (element instanceof DbcProof) {
                  element = ((DbcProof)element).getTarget();
               }
               TreeItem item = searchTreeItem(element);
               if (item != null) {
                  updateTreeItem(item);
               }
            }
         }
      });
   }

   /**
    * Searches the {@link TreeItem} that contains the given {@link Object}.
    * @param toSearch The {@link Object} for that the {@link TreeItem} is needed.
    * @return The found {@link TreeItem} or {@code null} if no one was found.
    */
   protected TreeItem searchTreeItem(Object toSearch) {
      return searchTreeItem(viewer.getTree().getItems(), toSearch);
   }

   /**
    * Searches recursive the {@link TreeItem} that contains the given {@link Object}.
    * @param items The current {@link TreeItem}s to search in.
    * @param toSearch The {@link Object} for that the {@link TreeItem} is needed.
    * @return The found {@link TreeItem} or {@code null} if no one was found.
    */
   protected TreeItem searchTreeItem(TreeItem[] items, Object toSearch) {
      TreeItem result = null;
      int i = 0;
      while (result == null && i < items.length) {
         if (ObjectUtil.equal(items[i].getData(), toSearch)) {
            result = items[i];
         }
         if (result == null) {
            result = searchTreeItem(items[i].getItems(), toSearch);
         }
         i++;
      }
      return result;
   } 
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (!viewer.getTree().isDisposed()) {
         viewer.getTree().removeTreeListener(treeListener);
      }
      if (viewer.getLabelProvider() != null) {
         viewer.getLabelProvider().removeListener(labelProviderListener);
      }
   }
   
   /**
    * Returns the observed {@link TreeViewer}.
    * @return The observed {@link TreeViewer}.
    */
   public TreeViewer getViewer() {
      return viewer;
   }
}