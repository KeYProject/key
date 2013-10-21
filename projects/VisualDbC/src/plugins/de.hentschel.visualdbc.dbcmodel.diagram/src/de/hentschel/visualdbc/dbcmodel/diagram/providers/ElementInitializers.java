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