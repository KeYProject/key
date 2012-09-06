package org.key_project.sed.ui.visualization.object_diagram.provider;

import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.tb.DefaultToolBehaviorProvider;
import org.eclipse.graphiti.tb.IToolBehaviorProvider;
import org.key_project.util.java.ObjectUtil;

/**
 * {@link IToolBehaviorProvider} specific implementation for object diagrams.
 * @author Martin Hentschel
 */
public class ObjectDiagramToolBehaviorProvider extends DefaultToolBehaviorProvider {
   /**
    * Constructor.
    * @param diagramTypeProvider The {@link IDiagramTypeProvider} in which this {@link IToolBehaviorProvider} is used.
    */
   public ObjectDiagramToolBehaviorProvider(IDiagramTypeProvider diagramTypeProvider) {
      super(diagramTypeProvider);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean equalsBusinessObjects(Object o1, Object o2) {
      return ObjectUtil.equals(o1, o2); // Used equals method instead of the default equality which returns true if both object contains the same values.
   }
}
