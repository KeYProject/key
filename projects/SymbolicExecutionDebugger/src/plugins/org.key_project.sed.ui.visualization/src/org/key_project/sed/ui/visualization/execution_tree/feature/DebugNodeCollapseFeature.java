package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.custom.ICustomFeature;

public class DebugNodeCollapseFeature extends AbstractDebugNodeCollapseFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link ICustomFeature}.
    */
   public DebugNodeCollapseFeature(IFeatureProvider fp) {
      super(fp);
   }
}