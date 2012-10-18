package org.key_project.sed.ui.visualization.object_diagram.feature;

import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.IResizeShapeFeature;
import org.eclipse.graphiti.features.context.IResizeShapeContext;
import org.eclipse.graphiti.features.impl.DefaultResizeShapeFeature;
import org.key_project.sed.ui.visualization.model.od.ODValue;

/**
 * Implementation of {@link IResizeShapeFeature} for {@link ODValue}s.
 * @author Martin Hentschel
 */
public class ValueResizeFeature extends DefaultResizeShapeFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IResizeShapeFeature}.
    */
   public ValueResizeFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canResizeShape(IResizeShapeContext context) {
      return false;
   }
}
