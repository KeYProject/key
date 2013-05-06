/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

import java.util.List;

import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.edit.provider.ComposedAdapterFactory;
import org.eclipse.emf.edit.provider.INotifyChangedListener;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.widgets.TreeItem;

import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofObligation;
import de.hentschel.visualdbc.statistic.ui.util.StatisticUtil.ProofStatus;

/**
 * Modifies the used colors of {@link TreeItem} in a {@link TreeViewer} 
 * that uses providers based on a {@link ComposedAdapterFactory}.
 * @author Martin Hentschel
 */
public class StatisticColorDecorator extends AbstractTreeItemDecorator {
   /**
    * The {@link Color} to show for {@link ProofStatus#FULFILLED}.
    */
   private Color fulfilledColor;
   
   /**
    * The {@link Color} to show for {@link ProofStatus#OPEN}.
    */
   private Color openColor;
   
   /**
    * The {@link Color} to show for {@link ProofStatus#FAILED}.
    */
   private Color failedColor;

   /**
    * The {@link Color} to show for {@link ProofStatus#INVALID} or {@link ProofStatus#NOT_AVAILABLE}.
    */
   private Color defaultColor;
   
   /**
    * The index of the first column that contains a proof obligation.
    */
   private int firstProofObligationColumn;
   
   /**
    * The available proof obligations.
    */
   private List<DbcProofObligation> proofObligations;

   /**
    * The used {@link ComposedAdapterFactory}.
    */
   private ComposedAdapterFactory adapterFactory;   
   
   /**
    * Listens for changes on {@link #adapterFactory}.
    */
   private INotifyChangedListener adapterListener = new INotifyChangedListener() {
      @Override
      public void notifyChanged(Notification notification) {
         handleNotifyChanged(notification);
      }
   };
   
   /**
    * Constructor.
    * @param viewer The observed {@link TreeViewer}.
    * @param firstProofObligationColumn The index of the first column that contains a proof obligation.
    * @param proofObligations  The available proof obligations.
    */
   public StatisticColorDecorator(TreeViewer viewer, 
                                  int firstProofObligationColumn,
                                  List<DbcProofObligation> proofObligations,
                                  ComposedAdapterFactory adapterFactory) {
      super(viewer);
      this.firstProofObligationColumn = firstProofObligationColumn;
      this.proofObligations = proofObligations;
      this.adapterFactory = adapterFactory;
      fulfilledColor = new Color(viewer.getTree().getDisplay(), 0, 128, 0);
      openColor = new Color(viewer.getTree().getDisplay(), 255, 128, 0);
      failedColor = new Color(viewer.getTree().getDisplay(), 128, 0, 0);
      defaultColor = viewer.getTree().getDisplay().getSystemColor(SWT.COLOR_LIST_FOREGROUND);
      if (adapterFactory != null) {
         adapterFactory.addListener(adapterListener);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void updateTreeItem(TreeItem item) {
      if (item != null) {
         // Update obligation colors
         int i = firstProofObligationColumn;
         for (DbcProofObligation obligation : proofObligations) {
            ProofStatus status = StatisticUtil.getProofStatus(item.getData(), obligation);
            if (ProofStatus.FULFILLED.equals(status)) {
               item.setForeground(i, fulfilledColor);
            }
            else if (ProofStatus.OPEN.equals(status)) {
               item.setForeground(i, openColor);
            }
            else if (ProofStatus.FAILED.equals(status)) {
               item.setForeground(i, failedColor);
            }
            else {
               item.setForeground(i, defaultColor);
            }
            i++;
         }
         // Update maximal color
         ProofStatus maxStatus = computeRowObjectStatus(item.getData());
         if (ProofStatus.FULFILLED.equals(maxStatus)) {
            item.setForeground(fulfilledColor);
         }
         else if (ProofStatus.OPEN.equals(maxStatus)) {
            item.setForeground(openColor);
         }
         else if (ProofStatus.FAILED.equals(maxStatus)) {
            item.setForeground(failedColor);
         }
         else {
            item.setForeground(defaultColor);
         }
         // Update parents recursive
         updateTreeItem(item.getParentItem());
      }
   }

   /**
    * Computes the {@link ProofStatus} for the whole row {@link Object}.
    * @param rowObject The row {@link Object} to compute the {@link ProofStatus} for.
    * @return The computed {@link ProofStatus}.
    */
   protected ProofStatus computeRowObjectStatus(Object rowObject) {
      // Compute status of this row
      ProofStatus minStatus = ProofStatus.FULFILLED;
      for (DbcProofObligation obligation : proofObligations) {
         ProofStatus obligationStatus = StatisticUtil.getProofStatus(rowObject, obligation);
         if (!ProofStatus.INVALID.equals(obligationStatus)) {
            minStatus = ProofStatus.min(minStatus, obligationStatus);
         }
      }
      
      // Return minimal status based on the statuses of the children
      if (getViewer().getContentProvider() instanceof ITreeContentProvider) {
         ITreeContentProvider provider = (ITreeContentProvider)getViewer().getContentProvider();
         Object[] children = provider.getChildren(rowObject);
         for (Object childObject : children) {
            ProofStatus childStatus = computeRowObjectStatus(childObject);
            if (!ProofStatus.INVALID.equals(childStatus)) {
               minStatus = ProofStatus.min(minStatus, childStatus);
            }
         }
      }
      return minStatus;
   }
   
   /**
    * When something has changed on {@link #adapterFactory}.
    * @param notification The notification event.
    */
   protected void handleNotifyChanged(Notification notification) {
      TreeItem item = findVisibleItem(notification.getNotifier());
      if (item != null) {
         updateTreeItem(item);
      }
   }

   /**
    * Finds the visible {@link TreeItem} for the given element.
    * @param element The element for that the {@link TreeItem} is required.
    * @return The found {@link TreeItem} or {@code null} if no one could be found.
    */
   protected TreeItem findVisibleItem(Object element) {
      // Map proofs to target (proofs are not visible in the hierarchy)
      if (element instanceof DbcProof) {
         element = ((DbcProof)element).getTarget();
      }
      // Search item
      TreeItem item = searchTreeItem(element);
      if (item == null) {
         // Search parent
         EObject parent = null;
         if (element instanceof EObject) {
            parent = ((EObject)element).eContainer();
         }
         if (parent != null) {
            item = findVisibleItem(parent);
         }
      }
      return item;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      super.dispose();
      if (adapterFactory != null) {
         adapterFactory.removeListener(adapterListener);
      }
      fulfilledColor.dispose();
      openColor.dispose();
      failedColor.dispose();
      defaultColor.dispose();
   }
}