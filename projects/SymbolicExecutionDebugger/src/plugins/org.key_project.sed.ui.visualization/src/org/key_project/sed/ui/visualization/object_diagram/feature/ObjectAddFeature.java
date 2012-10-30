package org.key_project.sed.ui.visualization.object_diagram.feature;

import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.pictograms.ContainerShape;
import org.eclipse.graphiti.services.IGaService;
import org.key_project.sed.ui.visualization.model.od.ODObject;

/**
 * Implementation of {@link IAddFeature} for {@link ODObject}s.
 * @author Martin Hentschel
 */
public class ObjectAddFeature extends AbstractODValueContainerAddFeature<ODObject> {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public ObjectAddFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean isNewObjectSupported(Object newObject) {
      return newObject instanceof ODObject;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected GraphicsAlgorithm createOuterBorder(IGaService gaService, ContainerShape containerShape) {
      return gaService.createRectangle(containerShape);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String computeName(ODObject addedObject) {
      return addedObject.getName() + " : " + addedObject.getType();
   }
}