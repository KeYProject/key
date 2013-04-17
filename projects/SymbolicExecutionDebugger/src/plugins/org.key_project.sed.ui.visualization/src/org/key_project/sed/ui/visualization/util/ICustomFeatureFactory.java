/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

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