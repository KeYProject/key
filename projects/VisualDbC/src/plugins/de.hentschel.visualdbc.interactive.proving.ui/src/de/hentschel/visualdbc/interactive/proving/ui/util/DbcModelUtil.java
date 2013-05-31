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

package de.hentschel.visualdbc.interactive.proving.ui.util;

import org.eclipse.emf.ecore.EObject;

import de.hentschel.visualdbc.dbcmodel.DbcModel;

/**
 * Provides static methods to work with dbc model instances.
 * @author Martin Hentschel
 */
public final class DbcModelUtil {
   /**
    * Forbid instances.
    */
   private DbcModelUtil() {
   }
   
   /**
    * Returns the {@link DbcModel} for the given {@link EObject} if possible.
    * @param object The current {@link EObject} that is a child of the {@link DbcModel}.
    * @return The found {@link DbcModel} or {@code null} if no one could be found for the {@link EObject}.
    */
   public static DbcModel getModelRoot(EObject object) {
      if (object != null) {
         if (object instanceof DbcModel) {
            return (DbcModel)object;
         }
         else {
            return getModelRoot(object.eContainer());
         }
      }
      else {
         return null;
      }
   }
}