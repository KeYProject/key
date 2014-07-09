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

import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.IAddContext;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.algorithms.Rectangle;
import org.eclipse.graphiti.mm.pictograms.ContainerShape;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.mm.pictograms.Shape;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.eclipse.graphiti.services.IPeCreateService;
import org.eclipse.graphiti.util.ColorConstant;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDMethodCall;
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
      ISEDDebugNode addedNode = (ISEDDebugNode) context.getNewObject();
      
      try {
         ISEDDebugNode parent = addedNode.getParent();
         PictogramElement pe = getFeatureProvider().getPictogramElementForBusinessObject(parent);
         boolean isInMethod = Boolean.parseBoolean(Graphiti.getPeService().getPropertyValue(pe, "isInMethod"));
         
         IPeCreateService peCreateService = Graphiti.getPeCreateService();
         IGaService gaService = Graphiti.getGaService();
         
         ContainerShape invisContainer;
         Diagram targetDiagram = (Diagram) context.getTargetContainer();
         invisContainer = peCreateService.createContainerShape(targetDiagram, true);
         if(isInMethod)
         {
            while(!(parent instanceof ISEDMethodCall))
               parent = parent.getParent();
            
            ContainerShape parentMethod = (ContainerShape) getFeatureProvider().getPictogramElementForBusinessObject(parent);
//            invisContainer = peCreateService.createContainerShape(parentMethod, true);
//            invisContainer = peCreateService.createContainerShape(parentMethod, true);
            Graphiti.getPeService().setPropertyValue(invisContainer, "methodID", parent.getId());
         }
//         else
//         {
//            Diagram targetDiagram = (Diagram) context.getTargetContainer();
//            invisContainer = peCreateService.createContainerShape(targetDiagram, true);
//         }
            
         Rectangle inv = gaService.createInvisibleRectangle(invisContainer);
         link(invisContainer, addedNode);
         
         Shape rectShape = peCreateService.createShape(invisContainer, false);
         
         Rectangle rect = gaService.createRectangle(rectShape);
         rect.setForeground(manageColor(new ColorConstant(255, 102, 0)));
         rect.setLineWidth(2);
         rect.setFilled(false);
         link(rectShape, addedNode);
         
         ContainerShape nodeContainer = createNodeDesign(addedNode, context);
         nodeContainer.setContainer(invisContainer);
         
         GraphicsAlgorithm ga = nodeContainer.getGraphicsAlgorithm();

         gaService.setLocationAndSize(inv, context.getX(), context.getY(), ga.getWidth(), ga.getHeight());
         gaService.setLocationAndSize(rect, 0, ga.getHeight() / 2, ga.getWidth(), ga.getHeight());
         gaService.setLocationAndSize(ga, 0, 0, ga.getWidth(), ga.getHeight());

         Graphiti.getPeService().setPropertyValue(invisContainer, "collapsed", "false");
         Graphiti.getPeService().setPropertyValue(invisContainer, "width", Integer.toString(inv.getWidth()));
         Graphiti.getPeService().setPropertyValue(invisContainer, "height", Integer.toString(inv.getHeight()));
         Graphiti.getPeService().setPropertyValue(invisContainer, "offX", Integer.toString(inv.getX()));
         Graphiti.getPeService().setPropertyValue(invisContainer, "offY", Integer.toString(inv.getY()));
         Graphiti.getPeService().setPropertyValue(invisContainer, "isInMethod", Boolean.toString(isInMethod));
         
         createAnchor(nodeContainer);
         
         return invisContainer;
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
      }

      return null;
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