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

import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.IStateListener;
import org.eclipse.core.commands.State;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.emf.common.ui.URIEditorInput;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.emf.workspace.util.WorkspaceSynchronizer;
import org.eclipse.gef.palette.PaletteRoot;
import org.eclipse.gmf.runtime.common.ui.services.marker.MarkerNavigationService;
import org.eclipse.gmf.runtime.diagram.core.preferences.PreferencesHint;
import org.eclipse.gmf.runtime.diagram.ui.actions.ActionIds;
import org.eclipse.gmf.runtime.diagram.ui.resources.editor.document.IDiagramDocument;
import org.eclipse.gmf.runtime.diagram.ui.resources.editor.document.IDocument;
import org.eclipse.gmf.runtime.diagram.ui.resources.editor.document.IDocumentProvider;
import org.eclipse.gmf.runtime.diagram.ui.resources.editor.parts.DiagramDocumentEditor;
import org.eclipse.gmf.runtime.notation.Diagram;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.window.Window;
import org.eclipse.osgi.util.NLS;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorMatchingStrategy;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.dialogs.SaveAsDialog;
import org.eclipse.ui.handlers.RadioState;
import org.eclipse.ui.handlers.RegistryToggleState;
import org.eclipse.ui.ide.IGotoMarker;
import org.eclipse.ui.navigator.resources.ProjectExplorer;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.part.IShowInTargetList;
import org.eclipse.ui.part.ShowInContext;

import de.hentschel.visualdbc.dbcmodel.diagram.navigator.DbCNavigatorItem;
import de.hentschel.visualdbc.dbcmodel.diagram.util.ProofReferenceManagement;

/**
 * @generated
 */
public class DbCDiagramEditor extends DiagramDocumentEditor implements
      IGotoMarker {

   /**
    * @generated
    */
   public static final String ID = "de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditorID"; //$NON-NLS-1$

   /**
    * @generated
    */
   public static final String CONTEXT_ID = "de.hentschel.visualdbc.dbcmodel.diagram.ui.diagramContext"; //$NON-NLS-1$

   /**
    * @generated
    */
   public DbCDiagramEditor() {
      super(true);
   }
   
   /**
    * @generated NOT
    */
   public DbCDiagramEditor(boolean hasFlyoutPalette) {
      super(hasFlyoutPalette);
   }

   /**
    * @generated
    */
   protected String getContextID() {
      return CONTEXT_ID;
   }

   /**
    * @generated
    */
   protected PaletteRoot createPaletteRoot(PaletteRoot existingPaletteRoot) {
      PaletteRoot root = super.createPaletteRoot(existingPaletteRoot);
      new DbCPaletteFactory().fillPalette(root);
      return root;
   }

   /**
    * @generated
    */
   protected PreferencesHint getPreferencesHint() {
      return DbCDiagramEditorPlugin.DIAGRAM_PREFERENCES_HINT;
   }

   /**
    * @generated
    */
   public String getContributorId() {
      return DbCDiagramEditorPlugin.ID;
   }

   /**
    * @generated
    */
   @SuppressWarnings("rawtypes")
   public Object getAdapter(Class type) {
      if (type == IShowInTargetList.class) {
         return new IShowInTargetList() {
            public String[] getShowInTargetIds() {
               return new String[] { ProjectExplorer.VIEW_ID };
            }
         };
      }
      return super.getAdapter(type);
   }

   /**
    * @generated
    */
   protected IDocumentProvider getDocumentProvider(IEditorInput input) {
      if (input instanceof IFileEditorInput || input instanceof URIEditorInput) {
         return DbCDiagramEditorPlugin.getInstance().getDocumentProvider();
      }
      return super.getDocumentProvider(input);
   }

   /**
    * @generated
    */
   public TransactionalEditingDomain getEditingDomain() {
      IDocument document = getEditorInput() != null ? getDocumentProvider()
            .getDocument(getEditorInput()) : null;
      if (document instanceof IDiagramDocument) {
         return ((IDiagramDocument) document).getEditingDomain();
      }
      return super.getEditingDomain();
   }

   /**
    * @generated
    */
   protected void setDocumentProvider(IEditorInput input) {
      if (input instanceof IFileEditorInput || input instanceof URIEditorInput) {
         setDocumentProvider(DbCDiagramEditorPlugin.getInstance()
               .getDocumentProvider());
      }
      else {
         super.setDocumentProvider(input);
      }
   }

   /**
    * @generated
    */
   public void gotoMarker(IMarker marker) {
      MarkerNavigationService.getInstance().gotoMarker(this, marker);
   }

   /**
    * @generated
    */
   public boolean isSaveAsAllowed() {
      return true;
   }

   /**
    * @generated
    */
   public void doSaveAs() {
      performSaveAs(new NullProgressMonitor());
   }

   /**
    * @generated
    */
   protected void performSaveAs(IProgressMonitor progressMonitor) {
      Shell shell = getSite().getShell();
      IEditorInput input = getEditorInput();
      SaveAsDialog dialog = new SaveAsDialog(shell);
      IFile original = input instanceof IFileEditorInput ? ((IFileEditorInput) input)
            .getFile() : null;
      if (original != null) {
         dialog.setOriginalFile(original);
      }
      dialog.create();
      IDocumentProvider provider = getDocumentProvider();
      if (provider == null) {
         // editor has been programmatically closed while the dialog was open
         return;
      }
      if (provider.isDeleted(input) && original != null) {
         String message = NLS.bind(Messages.DbCDiagramEditor_SavingDeletedFile,
               original.getName());
         dialog.setErrorMessage(null);
         dialog.setMessage(message, IMessageProvider.WARNING);
      }
      if (dialog.open() == Window.CANCEL) {
         if (progressMonitor != null) {
            progressMonitor.setCanceled(true);
         }
         return;
      }
      IPath filePath = dialog.getResult();
      if (filePath == null) {
         if (progressMonitor != null) {
            progressMonitor.setCanceled(true);
         }
         return;
      }
      IWorkspaceRoot workspaceRoot = ResourcesPlugin.getWorkspace().getRoot();
      IFile file = workspaceRoot.getFile(filePath);
      final IEditorInput newInput = new FileEditorInput(file);
      // Check if the editor is already open
      IEditorMatchingStrategy matchingStrategy = getEditorDescriptor()
            .getEditorMatchingStrategy();
      IEditorReference[] editorRefs = PlatformUI.getWorkbench()
            .getActiveWorkbenchWindow().getActivePage().getEditorReferences();
      for (int i = 0; i < editorRefs.length; i++) {
         if (matchingStrategy.matches(editorRefs[i], newInput)) {
            MessageDialog.openWarning(shell,
                  Messages.DbCDiagramEditor_SaveAsErrorTitle,
                  Messages.DbCDiagramEditor_SaveAsErrorMessage);
            return;
         }
      }
      boolean success = false;
      try {
         provider.aboutToChange(newInput);
         getDocumentProvider(newInput).saveDocument(progressMonitor, newInput,
               getDocumentProvider().getDocument(getEditorInput()), true);
         success = true;
      }
      catch (CoreException x) {
         IStatus status = x.getStatus();
         if (status == null || status.getSeverity() != IStatus.CANCEL) {
            ErrorDialog.openError(shell,
                  Messages.DbCDiagramEditor_SaveErrorTitle,
                  Messages.DbCDiagramEditor_SaveErrorMessage, x.getStatus());
         }
      }
      finally {
         provider.changed(newInput);
         if (success) {
            setInput(newInput);
         }
      }
      if (progressMonitor != null) {
         progressMonitor.setCanceled(!success);
      }
   }

   /**
    * @generated
    */
   public ShowInContext getShowInContext() {
      return new ShowInContext(getEditorInput(), getNavigatorSelection());
   }

   /**
    * @generated
    */
   private ISelection getNavigatorSelection() {
      IDiagramDocument document = getDiagramDocument();
      if (document == null) {
         return StructuredSelection.EMPTY;
      }
      Diagram diagram = document.getDiagram();
      if (diagram == null || diagram.eResource() == null) {
         return StructuredSelection.EMPTY;
      }
      IFile file = WorkspaceSynchronizer.getFile(diagram.eResource());
      if (file != null) {
         DbCNavigatorItem item = new DbCNavigatorItem(diagram, file, false);
         return new StructuredSelection(item);
      }
      return StructuredSelection.EMPTY;
   }

   /**
    * @generated
    */
   protected void configureGraphicalViewer() {
      super.configureGraphicalViewer();
      DiagramEditorContextMenuProvider provider = new DiagramEditorContextMenuProvider(
            this, getDiagramGraphicalViewer());
      getDiagramGraphicalViewer().setContextMenu(provider);
      getSite().registerContextMenu(ActionIds.DIAGRAM_EDITOR_CONTEXT_MENU,
            provider, getDiagramGraphicalViewer());
   }
   
   //###########################################################################
   //### Begin custom code for proof reference management ######################
   //###########################################################################
   
   /**
    * @generated NOT
    */
   private IStateListener stateListener = new IStateListener() {
      @Override
      public void handleStateChange(State state, Object oldValue) {
         updateProofReferenceManagement();
      }
   };
   
   /**
    * @generated NOT
    */
   private State hideState;
   
   /**
    * @generated NOT
    */
   private State highlightState;
   
   /**
    * @generated NOT
    */
   @Override
   public void init(IEditorSite site, IEditorInput input) throws PartInitException {
      super.init(site, input);
      ICommandService service = (ICommandService)PlatformUI.getWorkbench().getService(ICommandService.class);
      if (service != null) {
         Command hideCmd = service.getCommand("de.hentschel.visualdbc.dbcmodel.diagram.defineProofReferencesCommand");
         if (hideCmd != null) {
            hideState = hideCmd.getState(RadioState.STATE_ID);
            if (hideState != null) {
               hideState.addListener(stateListener);
            }
         }
         Command highlightCmd = service.getCommand("de.hentschel.visualdbc.dbcmodel.diagram.highlightProofReferencesCommand");
         if (highlightCmd != null) {
            highlightState = highlightCmd.getState(RegistryToggleState.STATE_ID);
            if (highlightState != null) {
               highlightState.addListener(stateListener);
            }
         }
      }
   }

   /**
    * @generated NOT
    */
   protected void handleSelectionChanged() {
      super.handleSelectionChanged();
      updateProofReferenceManagement();
   }

   /**
    * @generated NOT
    */
   protected void updateProofReferenceManagement() {
      ISelection selection = getSite().getSelectionProvider().getSelection();
      if (highlightState != null) {
         ProofReferenceManagement.updateHighlighting(this, selection, highlightState.getValue());
      }
      if (hideState != null) {
         ProofReferenceManagement.updateHiddenElements(this, selection, hideState.getValue());
      }
   }

   /**
    * @generated NOT
    */
   @Override
   public void dispose() {
      if (hideState != null) {
         hideState.removeListener(stateListener);
      }
      if (highlightState != null) {
         highlightState.removeListener(stateListener);
      }
      super.dispose();
   }
   
   //###########################################################################
   //### End custom code for proof reference management ########################
   //###########################################################################
}