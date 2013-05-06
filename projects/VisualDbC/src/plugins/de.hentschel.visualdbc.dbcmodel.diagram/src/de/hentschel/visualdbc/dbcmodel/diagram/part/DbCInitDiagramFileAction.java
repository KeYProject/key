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

import org.eclipse.core.resources.IFile;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.common.util.WrappedException;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.gmf.runtime.emf.core.GMFEditingDomainFactory;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.osgi.util.NLS;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcModelEditPart;

/**
 * @generated
 */
public class DbCInitDiagramFileAction implements IObjectActionDelegate {

   /**
    * @generated
    */
   private IWorkbenchPart targetPart;

   /**
    * @generated
    */
   private URI domainModelURI;

   /**
    * @generated
    */
   public void setActivePart(IAction action, IWorkbenchPart targetPart) {
      this.targetPart = targetPart;
   }

   /**
    * @generated
    */
   public void selectionChanged(IAction action, ISelection selection) {
      domainModelURI = null;
      action.setEnabled(false);
      if (selection instanceof IStructuredSelection == false
            || selection.isEmpty()) {
         return;
      }
      IFile file = (IFile) ((IStructuredSelection) selection).getFirstElement();
      domainModelURI = URI.createPlatformResourceURI(file.getFullPath()
            .toString(), true);
      action.setEnabled(true);
   }

   /**
    * @generated
    */
   private Shell getShell() {
      return targetPart.getSite().getShell();
   }

   /**
    * @generated
    */
   public void run(IAction action) {
      TransactionalEditingDomain editingDomain = GMFEditingDomainFactory.INSTANCE
            .createEditingDomain();
      ResourceSet resourceSet = editingDomain.getResourceSet();
      EObject diagramRoot = null;
      try {
         Resource resource = resourceSet.getResource(domainModelURI, true);
         diagramRoot = (EObject) resource.getContents().get(0);
      }
      catch (WrappedException ex) {
         DbCDiagramEditorPlugin.getInstance().logError(
               "Unable to load resource: " + domainModelURI, ex); //$NON-NLS-1$
      }
      if (diagramRoot == null) {
         MessageDialog.openError(getShell(),
               Messages.InitDiagramFile_ResourceErrorDialogTitle,
               Messages.InitDiagramFile_ResourceErrorDialogMessage);
         return;
      }
      Wizard wizard = new DbCNewDiagramFileWizard(domainModelURI, diagramRoot,
            editingDomain);
      wizard.setWindowTitle(NLS.bind(Messages.InitDiagramFile_WizardTitle,
            DbcModelEditPart.MODEL_ID));
      DbCDiagramEditorUtil.runWizard(getShell(), wizard, "InitDiagramFile"); //$NON-NLS-1$
   }
}