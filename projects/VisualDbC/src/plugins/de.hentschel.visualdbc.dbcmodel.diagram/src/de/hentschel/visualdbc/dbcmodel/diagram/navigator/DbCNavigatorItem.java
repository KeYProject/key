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

package de.hentschel.visualdbc.dbcmodel.diagram.navigator;

import org.eclipse.core.runtime.IAdapterFactory;
import org.eclipse.core.runtime.Platform;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.util.EcoreUtil;
import org.eclipse.gmf.runtime.notation.View;

/**
 * @generated
 */
public class DbCNavigatorItem extends DbCAbstractNavigatorItem {

   /**
    * @generated
    */
   static {
      final Class[] supportedTypes = new Class[] { View.class, EObject.class };
      Platform.getAdapterManager().registerAdapters(
            new IAdapterFactory() {

               public Object getAdapter(Object adaptableObject,
                     Class adapterType) {
                  if (adaptableObject instanceof de.hentschel.visualdbc.dbcmodel.diagram.navigator.DbCNavigatorItem
                        && (adapterType == View.class || adapterType == EObject.class)) {
                     return ((de.hentschel.visualdbc.dbcmodel.diagram.navigator.DbCNavigatorItem) adaptableObject)
                           .getView();
                  }
                  return null;
               }

               public Class[] getAdapterList() {
                  return supportedTypes;
               }
            },
            de.hentschel.visualdbc.dbcmodel.diagram.navigator.DbCNavigatorItem.class);
   }

   /**
    * @generated
    */
   private View myView;

   /**
    * @generated
    */
   private boolean myLeaf = false;

   /**
    * @generated
    */
   public DbCNavigatorItem(View view, Object parent, boolean isLeaf) {
      super(parent);
      myView = view;
      myLeaf = isLeaf;
   }

   /**
    * @generated
    */
   public View getView() {
      return myView;
   }

   /**
    * @generated
    */
   public boolean isLeaf() {
      return myLeaf;
   }

   /**
    * @generated
    */
   public boolean equals(Object obj) {
      if (obj instanceof de.hentschel.visualdbc.dbcmodel.diagram.navigator.DbCNavigatorItem) {
         return EcoreUtil
               .getURI(getView())
               .equals(
                     EcoreUtil
                           .getURI(((de.hentschel.visualdbc.dbcmodel.diagram.navigator.DbCNavigatorItem) obj)
                                 .getView()));
      }
      return super.equals(obj);
   }

   /**
    * @generated
    */
   public int hashCode() {
      return EcoreUtil.getURI(getView()).hashCode();
   }

}