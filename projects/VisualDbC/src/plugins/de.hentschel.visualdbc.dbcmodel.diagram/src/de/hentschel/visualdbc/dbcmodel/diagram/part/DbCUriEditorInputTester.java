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
