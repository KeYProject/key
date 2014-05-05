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

package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.IUpdateFeature;
import org.key_project.sed.core.model.ISEDLoopCondition;

/**
 * Implementation of {@link IUpdateFeature} for {@link ISEDLoopCondition}s.
 * @author Martin Hentschel
 */
public class LoopConditionUpdateFeature extends AbstractDebugNodeUpdateFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IUpdateFeature}.
    */   
   public LoopConditionUpdateFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean canUpdateBusinessObject(Object businessObject) {
      return businessObject instanceof ISEDLoopCondition;
   }
}