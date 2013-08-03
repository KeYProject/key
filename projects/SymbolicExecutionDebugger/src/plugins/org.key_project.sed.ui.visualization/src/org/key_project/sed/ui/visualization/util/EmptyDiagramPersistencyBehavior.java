package org.key_project.sed.ui.visualization.util;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.transaction.RecordingCommand;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.ui.editor.DefaultPersistencyBehavior;
import org.eclipse.graphiti.ui.editor.DiagramBehavior;
import org.eclipse.graphiti.ui.editor.DiagramEditor;
import org.eclipse.graphiti.ui.editor.DiagramEditorInput;
import org.eclipse.graphiti.ui.services.GraphitiUi;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeDiagramTypeProvider;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.util.java.IOUtil;

/**
 * An extended {@link DefaultPersistencyBehavior} which allows to create
 * an empty diagram if {@link #EMPTY_DIAGRAM_URI} is used as {@link URI}
 * in the {@link DiagramEditorInput} loaded in a {@link DiagramEditor}.
 * @author Martin Hentschel
 */
public class EmptyDiagramPersistencyBehavior extends DefaultPersistencyBehavior {
   /**
    * This URL should be used to create an empty diagram.
    */
   public static final URI EMPTY_DIAGRAM_URI = URI.createGenericURI("emptyDiagram", "newEmptyDiagram", null);

   /**
    * The scheme used for empty diagram {@link URI}s.
    */
   public static final String SCHEME = EMPTY_DIAGRAM_URI.scheme();

   /**
    * Constructor.
    * @param diagramBehavior The {@link DiagramBehavior} in which this {@link DefaultPersistencyBehavior} is used.
    */
   public EmptyDiagramPersistencyBehavior(DiagramBehavior diagramBehavior) {
      super(diagramBehavior);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Diagram loadDiagram(URI uri) {
      if (SCHEME.equals(uri.scheme())) {
         TransactionalEditingDomain domain = diagramBehavior.getEditingDomain();
         if (domain != null) {
            // Create empty diagram
            final Diagram diagram = Graphiti.getPeCreateService().createDiagram(ExecutionTreeDiagramTypeProvider.TYPE, 
                                                                                IOUtil.getFileNameWithoutExtension("Empty Diagram"), 
                                                                                true);
            URI domainURI = URI.createURI("INVALID" + ExecutionTreeUtil.DOMAIN_FILE_EXTENSION_WITH_DOT);
            GraphitiUi.getPeService().setPropertyValue(diagram, ExecutionTreeUtil.USER_PROPERTY_DOMAIN_MODEL_FILE, domainURI.toString());
            // Create Resource
            final Resource resource = domain.getResourceSet().createResource(uri);
            if (diagram != null) {
               domain.getCommandStack().execute(new RecordingCommand(domain) {
                  @Override
                  protected void doExecute() {
                     resource.getContents().add(diagram);
                  }

                  @Override
                  public boolean canUndo() {
                     return false;
                  }
               });
            }
            return diagram;
         }
         else {
            return null; // Loading not possible without editing domain, same behavior as super class.
         }
      }
      else {
         return super.loadDiagram(uri);
      }
   }
}
