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

package de.hentschel.visualdbc.dbcmodel.diagram.navigator;

import org.eclipse.core.runtime.IAdapterFactory;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.PlatformObject;
import org.eclipse.ui.views.properties.tabbed.ITabbedPropertySheetPageContributor;

/**
 * @generated
 */
public abstract class DbCAbstractNavigatorItem extends PlatformObject {

   /**
    * @generated
    */
   static {
      final Class[] supportedTypes = new Class[] { ITabbedPropertySheetPageContributor.class };
      final ITabbedPropertySheetPageContributor propertySheetPageContributor = new ITabbedPropertySheetPageContributor() {
         public String getContributorId() {
            return "de.hentschel.visualdbc.dbcmodel.diagram"; //$NON-NLS-1$
         }
      };
      Platform.getAdapterManager().registerAdapters(
            new IAdapterFactory() {

               public Object getAdapter(Object adaptableObject,
                     Class adapterType) {
                  if (adaptableObject instanceof de.hentschel.visualdbc.dbcmodel.diagram.navigator.DbCAbstractNavigatorItem
                        && adapterType == ITabbedPropertySheetPageContributor.class) {
                     return propertySheetPageContributor;
                  }
                  return null;
               }

               public Class[] getAdapterList() {
                  return supportedTypes;
               }
            },
            de.hentschel.visualdbc.dbcmodel.diagram.navigator.DbCAbstractNavigatorItem.class);
   }

   /**
    * @generated
    */
   private Object myParent;

   /**
    * @generated
    */
   protected DbCAbstractNavigatorItem(Object parent) {
      myParent = parent;
   }

   /**
    * @generated
    */
   public Object getParent() {
      return myParent;
   }

}