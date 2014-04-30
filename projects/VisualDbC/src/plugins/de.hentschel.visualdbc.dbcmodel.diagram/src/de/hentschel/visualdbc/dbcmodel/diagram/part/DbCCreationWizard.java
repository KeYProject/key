/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
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

import java.lang.reflect.InvocationTargetException;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.actions.WorkspaceModifyOperation;

/**
 * @generated
 */
public class DbCCreationWizard extends Wizard implements INewWizard {

   /**
    * @generated
    */
   private IWorkbench workbench;

   /**
    * @generated
    */
   protected IStructuredSelection selection;

   /**
    * @generated
    */
   protected DbCCreationWizardPage diagramModelFilePage;

   /**
    * @generated
    */
   protected DbCCreationWizardPage domainModelFilePage;

   /**
    * @generated
    */
   protected Resource diagram;

   /**
    * @generated
    */
   private boolean openNewlyCreatedDiagramEditor = true;

   /**
    * @generated
    */
   public IWorkbench getWorkbench() {
      return workbench;
   }

   /**
    * @generated
    */
   public IStructuredSelection getSelection() {
      return selection;
   }

   /**
    * @generated
    */
   public final Resource getDiagram() {
      return diagram;
   }

   /**
    * @generated
    */
   public final boolean isOpenNewlyCreatedDiagramEditor() {
      return openNewlyCreatedDiagramEditor;
   }

   /**
    * @generated
    */
   public void setOpenNewlyCreatedDiagramEditor(
         boolean openNewlyCreatedDiagramEditor) {
      this.openNewlyCreatedDiagramEditor = openNewlyCreatedDiagramEditor;
   }

   /**
    * @generated
    */
   public void init(IWorkbench workbench, IStructuredSelection selection) {
      this.workbench = workbench;
      this.selection = selection;
      setWindowTitle(Messages.DbCCreationWizardTitle);
      setDefaultPageImageDescriptor(DbCDiagramEditorPlugin
            .getBundledImageDescriptor("icons/wizban/NewDbcmodelWizard.gif")); //$NON-NLS-1$
      setNeedsProgressMonitor(true);
   }

   /**
    * @generated
    */
   public void addPages() {
      diagramModelFilePage = new DbCCreationWizardPage(
            "DiagramModelFile", getSelection(), "dbc_diagram"); //$NON-NLS-1$ //$NON-NLS-2$
      diagramModelFilePage
            .setTitle(Messages.DbCCreationWizard_DiagramModelFilePageTitle);
      diagramModelFilePage
            .setDescription(Messages.DbCCreationWizard_DiagramModelFilePageDescription);
      addPage(diagramModelFilePage);

      domainModelFilePage = new DbCCreationWizardPage(
            "DomainModelFile", getSelection(), "dbc") { //$NON-NLS-1$ //$NON-NLS-2$

         public void setVisible(boolean visible) {
            if (visible) {
               String fileName = diagramModelFilePage.getFileName();
               fileName = fileName.substring(0, fileName.length()
                     - ".dbc_diagram".length()); //$NON-NLS-1$
               setFileName(DbCDiagramEditorUtil.getUniqueFileName(
                     getContainerFullPath(), fileName, "dbc")); //$NON-NLS-1$
            }
            super.setVisible(visible);
         }
      };
      domainModelFilePage
            .setTitle(Messages.DbCCreationWizard_DomainModelFilePageTitle);
      domainModelFilePage
            .setDescription(Messages.DbCCreationWizard_DomainModelFilePageDescription);
      addPage(domainModelFilePage);
   }

   /**
    * @generated
    */
   public boolean performFinish() {
      IRunnableWithProgress op = new WorkspaceModifyOperation(null) {

         protected void execute(IProgressMonitor monitor) throws CoreException,
               InterruptedException {
            diagram = DbCDiagramEditorUtil.createDiagram(
                  diagramModelFilePage.getURI(), domainModelFilePage.getURI(),
                  monitor);
            if (isOpenNewlyCreatedDiagramEditor() && diagram != null) {
               try {
                  DbCDiagramEditorUtil.openDiagram(diagram);
               }
               catch (PartInitException e) {
                  ErrorDialog.openError(getContainer().getShell(),
                        Messages.DbCCreationWizardOpenEditorError, null,
                        e.getStatus());
               }
            }
         }
      };
      try {
         getContainer().run(false, true, op);
      }
      catch (InterruptedException e) {
         return false;
      }
      catch (InvocationTargetException e) {
         if (e.getTargetException() instanceof CoreException) {
            ErrorDialog.openError(getContainer().getShell(),
                  Messages.DbCCreationWizardCreationError, null,
                  ((CoreException) e.getTargetException()).getStatus());
         }
         else {
            DbCDiagramEditorPlugin.getInstance().logError(
                  "Error creating diagram", e.getTargetException()); //$NON-NLS-1$
         }
         return false;
      }
      return diagram != null;
   }
}