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

package de.hentschel.visualdbc.dbcmodel.diagram.part;

import org.eclipse.emf.common.ui.URIEditorInput;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorMatchingStrategy;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.PartInitException;

/**
 * @generated
 */
public class DbCMatchingStrategy implements IEditorMatchingStrategy {

   /**
    * @generated
    */
   public boolean matches(IEditorReference editorRef, IEditorInput input) {
      IEditorInput editorInput;
      try {
         editorInput = editorRef.getEditorInput();
      }
      catch (PartInitException e) {
         return false;
      }

      if (editorInput.equals(input)) {
         return true;
      }
      if (editorInput instanceof URIEditorInput
            && input instanceof URIEditorInput) {
         return ((URIEditorInput) editorInput).getURI().equals(
               ((URIEditorInput) input).getURI());
      }
      return false;
   }

}