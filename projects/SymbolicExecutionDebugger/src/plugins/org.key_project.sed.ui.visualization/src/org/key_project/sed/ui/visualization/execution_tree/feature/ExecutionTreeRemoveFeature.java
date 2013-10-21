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

package org.key_project.sed.ui.visualization.execution_tree.feature;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.IRemoveFeature;
import org.eclipse.graphiti.features.context.IContext;
import org.eclipse.graphiti.features.context.IRemoveContext;
import org.eclipse.graphiti.features.context.impl.RemoveContext;
import org.eclipse.graphiti.features.impl.DefaultRemoveFeature;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.util.ISEDIterator;
import org.key_project.sed.core.util.SEDPreorderIterator;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeFeatureProvider;

/**
 * <p>
 * Implementation of {@link IRemoveFeature} for {@link ISEDDebugNode}s
 * to make sure that the complete subtree of the selected {@link ISEDDebugNode}
 * is removed from the diagram.
 * </p>
 * <p> 
 * This feature is the only one which is used in the wohle execution tree diagram.
 * It means that {@link ExecutionTreeFeatureProvider#getRemoveFeature(IRemoveContext)}
 * always returns an instance of this class.
 * </p>
 * @author Martin Hentschel
 */
public class ExecutionTreeRemoveFeature extends DefaultRemoveFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} to use.
    */
   public ExecutionTreeRemoveFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canRemove(IRemoveContext context) {
      return super.canRemove(context) &&
             getFeatureProvider().getBusinessObjectForPictogramElement(context.getPictogramElement()) != null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void execute(IContext context) {
      try {
         if (context instanceof IRemoveContext) {
            // Instantiate IRemoveContext for each element in the sub tree
            List<IRemoveContext> children = new LinkedList<IRemoveContext>();
            PictogramElement pe = ((IRemoveContext)context).getPictogramElement();
            Object[] businessObjectsForPictogramElement = getAllBusinessObjectsForPictogramElement(pe);
            for (Object businessObject : businessObjectsForPictogramElement) {
               if (businessObject instanceof ISEDDebugElement) {
                  ISEDIterator iter = new SEDPreorderIterator((ISEDDebugElement)businessObject);
                  while (iter.hasNext()) {
                     ISEDDebugElement next = iter.next();
                     PictogramElement childPe = getFeatureProvider().getPictogramElementForBusinessObject(next);
                     if (childPe != null) {
                        children.add(new RemoveContext(childPe));
                     }
                  }
               }
            }
            // Remove the whole sub tree defined by the starting element in the given IContext
            for (IRemoveContext child : children) {
               remove(child);
            }
         }
      }
      catch (DebugException e) {
         throw new RuntimeException(e);
      }
   }
}