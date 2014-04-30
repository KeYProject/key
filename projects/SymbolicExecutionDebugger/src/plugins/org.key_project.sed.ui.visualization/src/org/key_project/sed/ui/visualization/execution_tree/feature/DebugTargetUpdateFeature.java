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

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.IUpdateFeature;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;

/**
 * Implementation of {@link IUpdateFeature} for {@link ISEDDebugTarget}s.
 * @author Martin Hentschel
 */
public class DebugTargetUpdateFeature extends AbstractDebugNodeUpdateFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IUpdateFeature}.
    */      
   public DebugTargetUpdateFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean canUpdateBusinessObject(Object businessObject) {
      return businessObject instanceof ISEDDebugTarget;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean isNameUpdateNeeded(PictogramElement pictogramElement) throws DebugException {
      return false; // Is never needed
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean haveAllBusinessObjectChildrenHaveGraphicalRepresentation(PictogramElement pictogramElement) throws DebugException {
      boolean childrenHavePictogramElement = true;
      Object[] bos = getAllBusinessObjectsForPictogramElement(pictogramElement);
      for (Object bo : bos) {
         if (bo instanceof ISEDDebugTarget) {
            ISEDThread[] threads = ((ISEDDebugTarget)bo).getSymbolicThreads();
            int i = 0;
            while (childrenHavePictogramElement && i < threads.length) {
               PictogramElement threadPE = getPictogramElementForBusinessObject(threads[i]);
               childrenHavePictogramElement = threadPE != null;
               i++;
            }
         }
      }
      return childrenHavePictogramElement;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean updateName(PictogramElement pictogramElement,
                                IProgressMonitor monitor) throws DebugException {
      return true; // Nothing to do
   }
}