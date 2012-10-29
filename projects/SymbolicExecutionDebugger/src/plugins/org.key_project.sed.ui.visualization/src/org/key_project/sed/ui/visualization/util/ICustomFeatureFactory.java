package org.key_project.sed.ui.visualization.util;

import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.custom.ICustomFeature;

/**
 * A factory which instantiates an {@link ICustomFeature}.
 * @author Martin Hentschel
 */
public interface ICustomFeatureFactory {
   /**
    * Instantiates a new {@link ICustomFeature} with help of the given {@link IFeatureProvider}.
    * @param fp The given {@link IFeatureProvider}.
    * @return The instantiated {@link ICustomFeature}.
    */
   public ICustomFeature createFeature(IFeatureProvider fp);
}
