package org.key_project.sed.key.ui.visualization.execution_tree.feature;

import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.custom.ICustomFeature;
import org.key_project.sed.ui.visualization.util.ICustomFeatureFactory;

/**
 * Instantiates {@link DebugNodeVisualizeConfigurationsFeature}s.
 * @author Martin Hentschel
 */
public class DebugNodeVisualizeConfigurationsFeatureFactory implements ICustomFeatureFactory {
   /**
    * {@inheritDoc}
    */
   @Override
   public ICustomFeature createFeature(IFeatureProvider fp) {
      return new DebugNodeVisualizeConfigurationsFeature(fp);
   }
}
