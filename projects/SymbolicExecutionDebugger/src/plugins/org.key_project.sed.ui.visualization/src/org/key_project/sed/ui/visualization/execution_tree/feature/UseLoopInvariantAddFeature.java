package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDUseLoopInvariant;
import org.key_project.sed.ui.visualization.execution_tree.provider.IExecutionTreeImageConstants;

/**
 * Implementation of {@link IAddFeature} for {@link ISEDUseLoopInvariant}s.
 * @author Martin Hentschel
 */
public class UseLoopInvariantAddFeature extends AbstractDebugNodeAddFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public UseLoopInvariantAddFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean canAddBusinessObject(Object businessObject) {
      return businessObject instanceof ISEDUseLoopInvariant;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getImageId(ISEDDebugNode node) {
      ISEDUseLoopInvariant invariantNode = (ISEDUseLoopInvariant)node;
      if (invariantNode.isInitiallyValid()) {
         return IExecutionTreeImageConstants.IMG_USE_LOOP_INVARIANT;
      }
      else {
         return IExecutionTreeImageConstants.IMG_USE_LOOP_INVARIANT_INITIALLY_INVALID;
      }
   }
}