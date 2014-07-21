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

package de.hentschel.visualdbc.statistic.ui.emfAdapter;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.emf.common.notify.AdapterFactory;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.emf.edit.command.CommandParameter;
import org.eclipse.emf.edit.provider.ITableItemLabelProvider;
import org.eclipse.emf.edit.provider.ItemProviderAdapter;

import de.hentschel.visualdbc.dbcmodel.DbcProofObligation;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.dbcmodel.provider.DbcModelItemProvider;
import de.hentschel.visualdbc.statistic.ui.util.StatisticUtil;

/**
 * Special {@link DbcModelItemProvider} in that children are filtered
 * for statistic purpose. That means that only provable children are returned.
 * @author Martin Hentschel
 */
public class StatisticDbcModelItemProvider extends DbcModelItemProvider implements ITableItemLabelProvider {
   /**
    * Constructor.
    * @param adapterFactory The parent {@link AdapterFactory}.
    */
   public StatisticDbcModelItemProvider(AdapterFactory adapterFactory) {
      super(adapterFactory);
   }

   /**
    * Returns the features of the children to show.
    * @param object The {@link Object}.
    * @return The features of the children to show.
    */
   protected Collection<? extends EStructuralFeature> getAnyChildrenFeatures(Object object) {
      Collection<EStructuralFeature> result = new LinkedList<EStructuralFeature>();
      result.add(DbcmodelPackage.Literals.ABSTRACT_DB_CCONTAINER__PACKAGES);
      result.add(DbcmodelPackage.Literals.ABSTRACT_DBC_TYPE_CONTAINER__TYPES);
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
}