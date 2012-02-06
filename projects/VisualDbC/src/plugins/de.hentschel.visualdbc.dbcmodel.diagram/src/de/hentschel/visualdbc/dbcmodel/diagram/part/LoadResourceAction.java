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

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.gmf.runtime.diagram.ui.parts.DiagramEditor;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;

/**
 * @generated
 */
public class LoadResourceAction extends AbstractHandler {
   /**
    * @generated
    */
   public Object execute(ExecutionEvent event) throws ExecutionException {
      IEditorPart diagramEditor = HandlerUtil.getActiveEditorChecked(event);
      Shell shell = diagramEditor.getEditorSite().getShell();
      assert diagramEditor instanceof DiagramEditor;
      TransactionalEditingDomain editingDomain = ((DiagramEditor) diagramEditor)
            .getEditingDomain();
      org.eclipse.emf.edit.ui.action.LoadResourceAction.LoadResourceDialog loadResourceDialog = new org.eclipse.emf.edit.ui.action.LoadResourceAction.LoadResourceDialog(
            shell, editingDomain);
      loadResourceDialog.open();
      return null;
   }

}
