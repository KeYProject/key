/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
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
import org.eclipse.graphiti.features.IReconnectionFeature;
import org.eclipse.graphiti.features.context.IReconnectionContext;
import org.eclipse.graphiti.features.impl.DefaultReconnectionFeature;
import org.key_project.sed.ui.visualization.model.od.ODAssociation;

/**
 * Implementation of {@link IReconnectionFeature} for {@link ODAssociation}s.
 * @author Martin Hentschel
 */
public class AssociationReconnectionFeature extends DefaultReconnectionFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IReconnectionFeature}.
    */
   public AssociationReconnectionFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canReconnect(IReconnectionContext context) {
      return false; // Reconnection is not supported because the Graphiti is buggy and swaps sometimes source and target in graphical representation but calls this feature with correct events leading in a missmatch between shown diagram and model.
   }
}