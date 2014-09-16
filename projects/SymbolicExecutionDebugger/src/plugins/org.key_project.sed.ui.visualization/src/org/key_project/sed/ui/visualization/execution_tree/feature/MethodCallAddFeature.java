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

import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.IAddContext;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.algorithms.Rectangle;
import org.eclipse.graphiti.mm.pictograms.ContainerShape;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.eclipse.graphiti.services.IPeCreateService;
import org.eclipse.graphiti.util.ColorConstant;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.util.SEDMethodPreorderIterator;
import org.key_project.sed.ui.visualization.execution_tree.provider.IExecutionTreeImageConstants;
import org.key_project.sed.ui.visualization.util.LogUtil;

/**
 * Implementation of {@link IAddFeature} for {@link ISEDMethodCall}s.
 * @author Martin Hentschel
 */
public class MethodCallAddFeature extends AbstractDebugNodeAddFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public MethodCallAddFeature(IFeatureProvider fp) {
      super(fp);
   }
   
   /**
    * {@inheritDoc}
    */
   public PictogramElement add(IAddContext context) {
      ISEDMethodCall addedNode = (ISEDMethodCall) context.getNewObject();

      IPeCreateService peCreateService = Graphiti.getPeCreateService();
      IGaService gaService = Graphiti.getGaService();
      
      Diagram targetDiagram = (Diagram) context.getTargetContainer();
      ContainerShape container = peCreateService.createContainerShape(targetDiagram, true);

      Rectangle rect = gaService.createRectangle(container);
      
      ColorConstant color = new ColorConstant(102, 80, 180);
      if(addedNode.isCollapsed()) {
         SEDMethodPreorderIterator iter = new SEDMethodPreorderIterator(addedNode);
         try {
            color = iter.allBranchesFinished() ? new ColorConstant(102, 180, 0) : new ColorConstant(255, 102, 0);
         }
         catch (DebugException e) {
            LogUtil.getLogger().logError(e);
         }
      }
      
      rect.setForeground(manageColor(color));
      rect.setLineWidth(2);
      rect.setFilled(false);
      link(container, addedNode);
      
      GraphicsAlgorithm ga = super.add(context).getGraphicsAlgorithm();

      gaService.setLocationAndSize(rect, context.getX(), context.getY() + ga.getHeight() / 2, ga.getWidth(), ga.getHeight());

      return container;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean canAddBusinessObject(Object businessObject) {
      return businessObject instanceof ISEDMethodCall;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getImageId(ISEDDebugNode node) {
      return IExecutionTreeImageConstants.IMG_METHOD_CALL;
   }
}