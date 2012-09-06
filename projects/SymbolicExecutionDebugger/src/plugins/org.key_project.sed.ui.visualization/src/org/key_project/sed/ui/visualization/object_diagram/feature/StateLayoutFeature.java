package org.key_project.sed.ui.visualization.object_diagram.feature;

import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.ILayoutFeature;
import org.key_project.sed.ui.visualization.model.od.ODState;

/**
 * Implementation of {@link ILayoutFeature} for {@link ODState}s.
 * @author Martin Hentschel
 */
public class StateLayoutFeature extends AbstractODValueContainerLayoutFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link ILayoutFeature}.
    */
   public StateLayoutFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean isBusinessObjectSupported(Object bo) {
      return bo instanceof ODState;
   }
}