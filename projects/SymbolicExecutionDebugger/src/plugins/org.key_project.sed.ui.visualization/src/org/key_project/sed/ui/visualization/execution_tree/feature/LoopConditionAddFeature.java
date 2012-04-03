package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.key_project.sed.core.model.ISEDLoopCondition;
import org.key_project.sed.ui.visualization.execution_tree.provider.IExecutionTreeImageConstants;

/**
 * Implementation of {@link IAddFeature} for {@link ISEDLoopCondition}s.
 * @author Martin Hentschel
 */
public class LoopConditionAddFeature extends AbstractDebugNodeAddFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public LoopConditionAddFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean canAddBusinessObject(Object businessObject) {
      return businessObject instanceof ISEDLoopCondition;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getImageId() {
      return IExecutionTreeImageConstants.IMG_LOOP_CONDITION;
   }
}