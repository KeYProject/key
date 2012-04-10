package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.IUpdateFeature;
import org.key_project.sed.core.model.ISEDExceptionalTermination;

/**
 * Implementation of {@link IUpdateFeature} for {@link ISEDExceptionalTermination}s.
 * @author Martin Hentschel
 */
public class ExceptionalTerminationUpdateFeature extends AbstractDebugNodeUpdateFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IUpdateFeature}.
    */   
   public ExceptionalTerminationUpdateFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean canUpdateBusinessObject(Object businessObject) {
      return businessObject instanceof ISEDExceptionalTermination;
   }
}
