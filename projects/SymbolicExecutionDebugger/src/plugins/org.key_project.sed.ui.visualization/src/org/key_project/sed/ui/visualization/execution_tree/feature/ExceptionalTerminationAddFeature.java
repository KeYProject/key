package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDExceptionalTermination;
import org.key_project.sed.ui.visualization.execution_tree.provider.IExecutionTreeImageConstants;

/**
 * Implementation of {@link IAddFeature} for {@link ISEDExceptionalTermination}s.
 * @author Martin Hentschel
 */
public class ExceptionalTerminationAddFeature extends AbstractDebugNodeAddFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public ExceptionalTerminationAddFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean canAddBusinessObject(Object businessObject) {
      return businessObject instanceof ISEDExceptionalTermination;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getImageId(ISEDDebugNode node) {
      return IExecutionTreeImageConstants.IMG_EXCEPTIONAL_TERMINATION;
   }
}