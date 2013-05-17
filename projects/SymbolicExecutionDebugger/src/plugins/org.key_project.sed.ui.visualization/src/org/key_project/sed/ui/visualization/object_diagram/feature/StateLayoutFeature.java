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

package org.key_project.sed.ui.visualization.object_diagram.feature;

import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.ILayoutFeature;
import org.key_project.sed.ui.visualization.model.od.ODState;

/**
 * Implementation of {@link ILayoutFeature} for {@link ODState}s.
 * @author Martin Hentschel
 */
public class StateLayoutFeature extends AbstractODValueContainerLayoutFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link ILayoutFeature}.
    */
   public StateLayoutFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean isBusinessObjectSupported(Object bo) {
      return bo instanceof ODState;
   }
}