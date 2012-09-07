package org.key_project.sed.ui.visualization.object_diagram.provider;

import org.eclipse.graphiti.dt.AbstractDiagramTypeProvider;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.tb.IToolBehaviorProvider;

/**
 * {@link IDiagramTypeProvider} specific implementation for object diagrams.
 * @author Martin Hentschel
 */
public class ObjectDiagramTypeProvider extends AbstractDiagramTypeProvider {
   /**
    * The type name which is the unique identifier in diagrams.
    */
   public static final String TYPE = "objectDiagram";

   /**
    * The provider ID of this {@link IDiagramTypeProvider}.
    */
   public static final String PROVIDER_ID = "org.key_project.sed.ui.graphiti.ObjectDiagramTypeProvider";

   /**
    * Contains the available {@link IToolBehaviorProvider}s which are instantiated
    * lazily via {@link #getAvailableToolBehaviorProviders()}.
    */
   private ObjectDiagramToolBehaviorProvider[] toolBehaviorProviders;
   
   /**
    * Constructor.
    */
   public ObjectDiagramTypeProvider() {
      super();
      setFeatureProvider(new ObjectDiagramFeatureProvider(this));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ObjectDiagramToolBehaviorProvider[] getAvailableToolBehaviorProviders() {
      if (toolBehaviorProviders == null) {
         toolBehaviorProviders = new ObjectDiagramToolBehaviorProvider[] {new ObjectDiagramToolBehaviorProvider(this)};
      }
      return toolBehaviorProviders;
   }
}
