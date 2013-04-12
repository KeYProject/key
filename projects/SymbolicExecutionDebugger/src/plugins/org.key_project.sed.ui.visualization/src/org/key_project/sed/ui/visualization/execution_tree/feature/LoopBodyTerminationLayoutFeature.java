package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.ILayoutFeature;
import org.key_project.sed.core.model.ISEDLoopBodyTermination;

/**
 * Implementation of {@link ILayoutFeature} for {@link ISEDLoopBodyTermination}s.
 * @author Martin Hentschel
 */
public class LoopBodyTerminationLayoutFeature extends AbstractDebugNodeLayoutFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public LoopBodyTerminationLayoutFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean canLayoutBusinessObject(Object businessObject) {
      return businessObject instanceof ISEDLoopBodyTermination;
   }
}