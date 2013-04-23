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

import org.eclipse.gmf.runtime.diagram.ui.parts.DiagramActionBarContributor;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.IWorkbenchPage;

/**
 * @generated
 */
public class DbCDiagramActionBarContributor extends DiagramActionBarContributor {

   /**
    * @generated
    */
   protected Class getEditorClass() {
      return DbCDiagramEditor.class;
   }

   /**
    * @generated
    */
   protected String getEditorId() {
      return DbCDiagramEditor.ID;
   }

   /**
    * @generated
    */
   public void init(IActionBars bars, IWorkbenchPage page) {
      super.init(bars, page);
      // print preview
      IMenuManager fileMenu = bars.getMenuManager().findMenuUsingPath(
            IWorkbenchActionConstants.M_FILE);
      assert fileMenu != null;
      fileMenu.remove("pageSetupAction"); //$NON-NLS-1$
   }
}