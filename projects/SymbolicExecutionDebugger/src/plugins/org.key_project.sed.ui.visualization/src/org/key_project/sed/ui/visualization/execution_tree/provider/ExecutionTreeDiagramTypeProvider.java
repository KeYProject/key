package org.key_project.sed.ui.visualization.execution_tree.provider;

import org.eclipse.graphiti.dt.AbstractDiagramTypeProvider;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.tb.IToolBehaviorProvider;

/**
 * {@link IDiagramTypeProvider} specific implementation for execution tree diagrams.
 * @author Martin Hentschel
 */
// TODO: Implement persistence of business objects
// TODO: Implement new wizard for new diagrams
// TODO: Refactor branch conditions as connection text
// TODO: Implement customized delete/remove feature to remove/delete the whole sub tree
public class ExecutionTreeDiagramTypeProvider extends AbstractDiagramTypeProvider {
   /**
    * The ID of the diagram type provided by this {@link IDiagramTypeProvider}.
    */
   public static final String DIAGRAM_TYPE_ID = "org.key_project.sed.ui.graphiti.ExecutionTreeDiagramType";
   
   /**
    * The provider ID of this {@link IDiagramTypeProvider}.
    */
   public static final String PROVIDER_ID = "org.key_project.sed.ui.graphiti.ExecutionTreeDiagramTypeProvider";
   
   /**
    * Contains the available {@link IToolBehaviorProvider}s which are instantiated
    * lazily via {@link #getAvailableToolBehaviorProviders()}.
    */
   private IToolBehaviorProvider[] toolBehaviorProviders;
   
   /**
    * Constructor.
    */
   public ExecutionTreeDiagramTypeProvider() {
      super();
      setFeatureProvider(new ExecutionTreeFeatureProvider(this));
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IToolBehaviorProvider[] getAvailableToolBehaviorProviders() {
      if (toolBehaviorProviders == null) {
         toolBehaviorProviders = new IToolBehaviorProvider[] {new ExecutionTreeToolBehaviorProvider(this)};
      }
      return toolBehaviorProviders;
   }
}