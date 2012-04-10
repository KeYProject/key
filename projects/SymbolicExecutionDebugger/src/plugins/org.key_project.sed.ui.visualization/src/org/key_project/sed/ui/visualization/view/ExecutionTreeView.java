package org.key_project.sed.ui.visualization.view;

import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.edit.command.AddCommand;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.ui.editor.DiagramEditorActionBarContributor;
import org.eclipse.graphiti.ui.editor.DiagramEditorFactory;
import org.eclipse.graphiti.ui.editor.DiagramEditorInput;
import org.eclipse.graphiti.ui.services.GraphitiUi;
import org.eclipse.ui.IEditorActionBarContributor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.key_project.sed.ui.visualization.execution_tree.editor.ExecutionTreeDiagramEditor;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeDiagramTypeProvider;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.util.java.IOUtil;

public class ExecutionTreeView extends AbstractDebugViewBasedEditorInViewView {
   /**
    * The message which is shown to the user if the debug view is not opened.
    */
   public static final String MESSAGE_DEBUG_VIEW_NOT_OPENED = "View \"Debug\" is not opened.";
   
   /**
    * Constructor.
    */
   public ExecutionTreeView() {
      setMessage(MESSAGE_DEBUG_VIEW_NOT_OPENED);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected IEditorPart createEditorPart() {
      ExecutionTreeDiagramEditor editor = new ExecutionTreeDiagramEditor();
      editor.setPaletteHidden(true);
      return editor;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected IEditorActionBarContributor createEditorActionBarContributor() {
      return new DiagramEditorActionBarContributor();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected IEditorInput getEditorInput() {
      // Create empty diagram
      Diagram diagram = Graphiti.getPeCreateService().createDiagram(ExecutionTreeDiagramTypeProvider.TYPE, 
                                                                    IOUtil.getFileNameWithoutExtension("Empty Diagram"), 
                                                                    true);
      URI domainURI = URI.createURI("INVALID" + ExecutionTreeUtil.DOMAIN_FILE_EXTENSION_WITH_DOT);
      GraphitiUi.getPeService().setPropertyValue(diagram, ExecutionTreeUtil.USER_PROPERTY_DOMAIN_MODEL_FILE, domainURI.toString());
      // Create editing domain and resource that contains the diagram
      TransactionalEditingDomain domain = DiagramEditorFactory.createResourceSetAndEditingDomain();
      Resource resource = domain.getResourceSet().createResource(URI.createURI("INVALID" + ExecutionTreeUtil.DIAGRAM_FILE_EXTENSION_WITH_DOT));
      domain.getCommandStack().execute(new AddCommand(domain, resource.getContents(), diagram));
      return DiagramEditorInput.createEditorInput(diagram, domain, ExecutionTreeDiagramTypeProvider.PROVIDER_ID, true);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean shouldHandleDebugView(IDebugView debugView) {
      return IDebugUIConstants.ID_DEBUG_VIEW.equals(debugView.getSite().getId());
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleDebugViewChanged(IDebugView oldDebugView, IDebugView newDebugView) {
      if (newDebugView != null) {
         setMessage(null);
      }
      else {
         setMessage(MESSAGE_DEBUG_VIEW_NOT_OPENED);
      }
   }
}
