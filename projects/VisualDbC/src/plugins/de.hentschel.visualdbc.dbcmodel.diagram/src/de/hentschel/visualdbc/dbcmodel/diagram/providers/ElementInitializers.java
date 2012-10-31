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

package de.hentschel.visualdbc.dbcmodel.diagram.providers;

import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditorPlugin;

/**
 * @generated
 */
public class ElementInitializers {

   protected ElementInitializers() {
      // use #getInstance to access cached instance
   }

   /**
    * @generated
    */
   public static ElementInitializers getInstance() {
      ElementInitializers cached = DbCDiagramEditorPlugin.getInstance()
            .getElementInitializers();
      if (cached == null) {
         DbCDiagramEditorPlugin.getInstance().setElementInitializers(
               cached = new ElementInitializers());
      }
      return cached;
   }
}
