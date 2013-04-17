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

import org.eclipse.jface.viewers.ViewerSorter;

import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry;

/**
 * @generated
 */
public class DbCNavigatorSorter extends ViewerSorter {

   /**
    * @generated
    */
   private static final int GROUP_CATEGORY = 7066;

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