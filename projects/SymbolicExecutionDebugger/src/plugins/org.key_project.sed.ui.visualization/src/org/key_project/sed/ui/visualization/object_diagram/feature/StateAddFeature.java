package org.key_project.sed.ui.visualization.object_diagram.feature;

import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.pictograms.ContainerShape;
import org.eclipse.graphiti.services.IGaService;
import org.key_project.sed.ui.visualization.model.od.ODState;

/**
 * Implementation of {@link IAddFeature} for {@link ODState}s.
 * @author Martin Hentschel
 */
public class StateAddFeature extends AbstractODValueContainerAddFeature<ODState> {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public StateAddFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean isNewObjectSupported(Object newObject) {
      return newObject instanceof ODState;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected GraphicsAlgorithm createOuterBorder(IGaService gaService, ContainerShape containerShape) {
      return gaService.createRoundedRectangle(containerShape, 20, 20);
   }
}