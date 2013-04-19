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

package de.hentschel.visualdbc.statistic.ui.emfAdapter;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.emf.common.notify.AdapterFactory;
import org.eclipse.emf.common.notify.Notification;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.emf.edit.command.CommandParameter;
import org.eclipse.emf.edit.provider.ITableItemLabelProvider;
import org.eclipse.emf.edit.provider.ItemProviderAdapter;
import org.eclipse.emf.edit.provider.ViewerNotification;
import org.eclipse.swt.widgets.Display;

import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofObligation;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.dbcmodel.provider.DbCAxiomContractItemProvider;
import de.hentschel.visualdbc.statistic.ui.util.StatisticUtil;

/**
 * Special {@link DbCAxiomContractItemProvider} in that children are filtered
 * for statistic purpose. That means that only provable children are returned.
 * @author Martin Hentschel
 */
public class StatisticDbcAxiomContractItemProvider extends DbCAxiomContractItemProvider implements ITableItemLabelProvider {
   /**
    * Constructor.
    * @param adapterFactory The parent {@link AdapterFactory}.
    */
   public StatisticDbcAxiomContractItemProvider(AdapterFactory adapterFactory) {
      super(adapterFactory);
   }

   /**
    * Returns the features of the children to show.
    * @param object The {@link Object}.
    * @return The features of the children to show.
    */
   protected Collection<? extends EStructuralFeature> getAnyChildrenFeatures(Object object) {
      Collection<EStructuralFeature> result = new LinkedList<EStructuralFeature>();
      return result;
   }
   
   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Copied code from {@link ItemProviderAdapter#getChildren(Object)} because
    * the method getAnyChildrenFeatures is private in {@link ItemProviderAdapter}
    * and it must be changed to filter the contained children.
    * </p>
    */
   @Override
   public Collection<?> getChildren(Object object) {
      ChildrenStore store = getChildrenStore(object);
      if (store != null)
      {
        return store.getChildren();
      }

      store = createChildrenStore(object);
      List<Object> result = store != null ? null : new ArrayList<Object>();
      EObject eObject = (EObject)object;

      for (EStructuralFeature feature : getAnyChildrenFeatures(object))
      {
        if (feature.isMany())
        {
          List<?> children = (List<?>)eObject.eGet(feature);
          int index = 0;
          for (Object unwrappedChild : children)
          {
            Object child = wrap(eObject, feature, unwrappedChild, index);
            if (store != null)
            {
              store.getList(feature).add(child);
            }
            else
            {
              result.add(child);
            }
            index++;
          }
        }
        else
        {
          Object child = eObject.eGet(feature);
          if (child != null)
          {
            child = wrap(eObject, feature, child, CommandParameter.NO_INDEX);
            if (store != null)
            {
              store.setValue(feature, child);
            }
            else
            {
              result.add(child);
            }
          }
        }
      }
      return store != null ? store.getChildren() : result;
   }

   /**
    * Returns the shown {@link DbCProofObligation}s in the columns.
    * @return The shown {@link DbCProofObligation} in the columns.
    */
   public List<DbcProofObligation> getColumnProofObligations() {
      if (getAdapterFactory() instanceof StatisticDbcmodelItemProviderAdapterFactory) {
         return ((StatisticDbcmodelItemProviderAdapterFactory)getAdapterFactory()).getColumnProofObligations();
      }
      else {
         return null;
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getColumnText(Object object, int columnIndex) {
      if (columnIndex == 0) {
         return super.getText(object);
      }
      else {
         return StatisticUtil.getColumnText(object, columnIndex, getColumnProofObligations());
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Object getColumnImage(Object object, int columnIndex) {
      if (columnIndex == 0) {
         return super.getImage(object);
      }
      else {
         return StatisticUtil.getColumnImage(object, columnIndex, getColumnProofObligations());
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void notifyChanged(Notification notification) {
      if (DbcmodelPackage.Literals.IDB_CPROVABLE__ALL_PROOFS.equals(notification.getFeature())) {
         // Update cell values when a proof was added or removed
         fireNotifyChangedThreadSave(new ViewerNotification(notification, notification.getNotifier(), false, true));
         // Remove listener from no longer required proofs
         if (notification.getOldValue() instanceof EObject) {
            ((EObject)notification.getOldValue()).eAdapters().remove(this);
         }
         // Add listener to new proofs (Listener are automatically removed at dispose())
         if (notification.getNewValue() instanceof EObject) {
            EObject eobj = (EObject)notification.getNewValue();
            if (!eobj.eAdapters().contains(this)) {
               eobj.eAdapters().add(this);
            }
         }
      }
      else if (DbcmodelPackage.Literals.IDB_CPROVABLE__PROOF_OBLIGATIONS.equals(notification.getFeature())) {
         // Update cell when a possible proof obligation was added or removed
         fireNotifyChangedThreadSave(new ViewerNotification(notification, notification.getNotifier(), false, true));
      }
      else if (DbcmodelPackage.Literals.DBC_PROOF__OBLIGATION.equals(notification.getFeature())) {
         if (notification.getNotifier() instanceof DbcProof) {
            // Update cell when the proof obligation on the proof has changed
            fireNotifyChangedThreadSave(new ViewerNotification(notification, ((DbcProof)notification.getNotifier()).getTarget(), false, true));
         }
      }
      else if (DbcmodelPackage.Literals.DBC_PROOF__STATUS.equals(notification.getFeature())) {
         if (notification.getNotifier() instanceof DbcProof) {
            // Update cell when the proof status on the proof has changed
            fireNotifyChangedThreadSave(new ViewerNotification(notification, ((DbcProof)notification.getNotifier()).getTarget(), false, true));
         }
      }
      else {
         super.notifyChanged(notification);
      }
   }
   
   /**
    * Thread save execution of {@link #fireNotifyChanged(Notification)}.
    * @param notification The {@link Notification} to throw.
    */
   protected void fireNotifyChangedThreadSave(final Notification notification) {
      Display.getDefault().syncExec(new Runnable() {
         @Override
         public void run() {
            fireNotifyChanged(notification);
         }
      });
   }
}