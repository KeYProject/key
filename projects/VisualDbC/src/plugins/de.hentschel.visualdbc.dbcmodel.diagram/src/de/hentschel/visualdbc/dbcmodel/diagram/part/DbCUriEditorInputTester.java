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

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.emf.common.ui.URIEditorInput;

/**
 * @generated
 */
public class DbCUriEditorInputTester extends PropertyTester {

   /**
    * @generated
    */
   public boolean test(Object receiver, String method, Object[] args,
         Object expectedValue) {
      if (false == receiver instanceof URIEditorInput) {
         return false;
      }
      URIEditorInput editorInput = (URIEditorInput) receiver;
      return "dbc_diagram".equals(editorInput.getURI().fileExtension()); //$NON-NLS-1$
   }

}