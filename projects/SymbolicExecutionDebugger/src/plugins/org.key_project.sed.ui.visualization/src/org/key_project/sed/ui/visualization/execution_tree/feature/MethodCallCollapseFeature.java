package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.platform.IPlatformImageConstants;
import org.key_project.sed.core.model.ISEDMethodCall;

public class MethodCallCollapseFeature extends AbstractDebugNodeCollapseFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link ICustomFeature}.
    */
   public MethodCallCollapseFeature(IFeatureProvider fp) {
      super(fp);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean canExecuteBusinessObject(Object businessObject) {
      return businessObject instanceof ISEDMethodCall;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return "Collapse/Expand Functionbody";
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getDescription() {
      return "Collapse/Expand the Functionbody";
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getImageId() {
      return IPlatformImageConstants.IMG_EDIT_COLLAPSE;
   }
}
