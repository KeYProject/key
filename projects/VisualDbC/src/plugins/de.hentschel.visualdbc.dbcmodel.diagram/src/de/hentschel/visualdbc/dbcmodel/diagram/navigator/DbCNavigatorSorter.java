/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package de.hentschel.visualdbc.dbcmodel.diagram.navigator;

import org.eclipse.jface.viewers.ViewerSorter;

import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry;

/**
 * @generated
 */
public class DbCNavigatorSorter extends ViewerSorter {

   /**
    * @generated
    */
   private static final int GROUP_CATEGORY = 7065;

   /**
    * @generated
    */
   public int category(Object element) {
      if (element instanceof DbCNavigatorItem) {
         DbCNavigatorItem item = (DbCNavigatorItem) element;
         return DbCVisualIDRegistry.getVisualID(item.getView());
      }
      return GROUP_CATEGORY;
   }

}
