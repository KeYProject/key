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
import org.key_project.sed.core.model.ISEBranchCondition;
import org.key_project.sed.core.model.ISEDebugElement;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEMethodCall;
import org.key_project.sed.core.model.ISENodeLink;
import org.key_project.sed.core.util.ISEIterator;
import org.key_project.sed.core.util.SEPreorderIterator;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeFeatureProvider;
import org.key_project.util.java.ArrayUtil;

/**
 * <p>
 * Implementation of {@link IRemoveFeature} for {@link ISENode}s
 * to make sure that the complete subtree of the selected {@link ISENode}
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
               if (businessObject instanceof ISEDebugElement) {
                  ISEIterator iter = new SEPreorderIterator((ISEDebugElement)businessObject);
                  while (iter.hasNext()) {
                     ISEDebugElement next = iter.next();
                     if (next instanceof ISENode) {
                        ISENode nextNode = (ISENode) next;
                        createRemoveContexs(nextNode.getOutgoingLinks(), children);
                        createRemoveContexs(nextNode.getIncomingLinks(), children);
                     }
                     
                     createRemoveContexs(next, children);
                     
                     if (next instanceof ISEMethodCall) {
                        ISEMethodCall mc =  (ISEMethodCall) next;
                        if (mc.isCollapsed()) {
                           for (ISEBranchCondition bc : mc.getMethodReturnConditions()) {
                              createRemoveContexs(bc, children);
                           }
                        }
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
   
   /**
    * Creates {@link IRemoveContext}s for each {@link ISENodeLink}.
    * @param links The {@link ISENodeLink}s to remove.
    * @param listToFill The result list to fill.
    */
   protected void createRemoveContexs(ISENodeLink[] links, List<IRemoveContext> listToFill) {
      if (!ArrayUtil.isEmpty(links)) {
         for (ISENodeLink link : links) {
            createRemoveContexs(link, listToFill);
         }
      }
   }
   
   /**
    * Creates {@link IRemoveContext}s for each {@link PictogramElement} of the given business object.
    * @param bo The business object.
    * @param listToFill The result list to fill.
    */
   protected void createRemoveContexs(Object bo, List<IRemoveContext> listToFill) {
      PictogramElement[] childPEs = getFeatureProvider().getAllPictogramElementsForBusinessObject(bo);
      for (PictogramElement childPE : childPEs) {
         if (childPE != null) {
            listToFill.add(new RemoveContext(childPE));
         }
      }
   }
}