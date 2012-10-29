package org.key_project.sed.ui.visualization.object_diagram.feature;

import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.IMoveShapeFeature;
import org.eclipse.graphiti.features.context.IMoveShapeContext;
import org.eclipse.graphiti.features.impl.DefaultMoveShapeFeature;
import org.key_project.sed.ui.visualization.model.od.ODValue;

/**
 * Implementation of {@link IMoveShapeFeature} for {@link ODValue}s.
 * @author Martin Hentschel
 */
public class ValueMoveFeature extends DefaultMoveShapeFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IMoveShapeFeature}.
    */
   public ValueMoveFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canMoveShape(IMoveShapeContext context) {
      return false;
   }
}
