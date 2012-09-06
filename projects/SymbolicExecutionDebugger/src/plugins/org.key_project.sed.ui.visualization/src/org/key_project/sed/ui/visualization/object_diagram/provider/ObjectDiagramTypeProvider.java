package org.key_project.sed.ui.visualization.object_diagram.provider;

import org.eclipse.graphiti.dt.AbstractDiagramTypeProvider;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;

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
    * Constructor.
    */
   public ObjectDiagramTypeProvider() {
      super();
      setFeatureProvider(new ObjectDiagramFeatureProvider(this));
   }
}
