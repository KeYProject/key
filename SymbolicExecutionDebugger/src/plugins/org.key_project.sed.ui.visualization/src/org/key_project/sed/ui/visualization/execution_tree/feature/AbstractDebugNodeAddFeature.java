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
import org.eclipse.graphiti.datatypes.IDimension;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.IAddContext;
import org.eclipse.graphiti.features.impl.AbstractAddShapeFeature;
import org.eclipse.graphiti.mm.GraphicsAlgorithmContainer;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.algorithms.Image;
import org.eclipse.graphiti.mm.algorithms.Polyline;
import org.eclipse.graphiti.mm.algorithms.Rectangle;
import org.eclipse.graphiti.mm.algorithms.RoundedRectangle;
import org.eclipse.graphiti.mm.algorithms.Text;
import org.eclipse.graphiti.mm.algorithms.styles.Font;
import org.eclipse.graphiti.mm.algorithms.styles.Orientation;
import org.eclipse.graphiti.mm.pictograms.AnchorContainer;
import org.eclipse.graphiti.mm.pictograms.ChopboxAnchor;
import org.eclipse.graphiti.mm.pictograms.Connection;
import org.eclipse.graphiti.mm.pictograms.ConnectionDecorator;
import org.eclipse.graphiti.mm.pictograms.ContainerShape;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.mm.pictograms.Shape;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.eclipse.graphiti.services.IPeCreateService;
import org.eclipse.graphiti.util.ColorConstant;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEGroupable;
import org.key_project.sed.core.util.NodeUtil;
import org.key_project.sed.core.util.SEGroupPreorderIterator;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeStyleUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.java.StringUtil;

/**
 * Provides a basic implementation of {@link IAddFeature} for {@link ISENode}s.
 * @author Martin Hentschel
 */
public abstract class AbstractDebugNodeAddFeature extends AbstractAddShapeFeature {
   /**
    * The margin to use.
    */
   public static final int MARGIN = 5;
   
   /**
    * The image width.
    */
   public static final int IMAGE_WIDTH = 16;
   
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public AbstractDebugNodeAddFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canAdd(IAddContext context) {
      boolean canAdd = false;
      if (canAddBusinessObject(context.getNewObject())) {
         if (context.getTargetContainer() instanceof Diagram) {
            canAdd = true;
         }
      }
      return canAdd;
   }
   
   /**
    * Checks if the give business object can be handled by this {@link IAddFeature}.
    * @param businessObject The business object to check.
    * @return {@code true} can add, {@code false} can not add.
    */
   protected abstract boolean canAddBusinessObject(Object businessObject);
   
   /**
    * {@inheritDoc}
    */
   @Override
   public PictogramElement add(IAddContext context) {
      ISENode addedNode = (ISENode) context.getNewObject();
      boolean groupingSupported = addedNode.getDebugTarget().isGroupingSupported();
      
      IPeCreateService peCreateService = Graphiti.getPeCreateService();
      IGaService gaService = Graphiti.getGaService();
      
      Diagram targetDiagram = (Diagram) context.getTargetContainer();
      
      // If the new node opens a group, we need to create the rect first
      if(groupingSupported && NodeUtil.canBeGrouped(addedNode)) {
         ISEGroupable groupStart = (ISEGroupable) addedNode;
         ContainerShape container = peCreateService.createContainerShape(targetDiagram, true);
         Rectangle rect = gaService.createRectangle(container);
         
         // Base color (blueish)
         ColorConstant color = new ColorConstant(102, 80, 180);
         if(groupStart.isCollapsed()) {
            SEGroupPreorderIterator iter = new SEGroupPreorderIterator(groupStart);
            try {
               // color group complete: greenish
               // color group not complete: redish
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
         
         GraphicsAlgorithm ga = createNode(context, groupingSupported).getGraphicsAlgorithm();

         gaService.setLocationAndSize(rect, context.getX(), context.getY() + ga.getHeight() / 2, ga.getWidth(), ga.getHeight() + ga.getHeight() / 2);

         return container;
      }
      else {
         // create the node
         return createNode(context, groupingSupported);
      }
   }
   
   /**
    * Creates the node with rounded rect, image, text, anchor and connection.
    * @param context The {@link IAddContext} for this node.
    * @param groupingSupported Is grouping supported?
    * @return The {@link PictogramElement} for this node.
    */
   private PictogramElement createNode(IAddContext context, boolean groupingSupported) {
      ISENode addedNode = (ISENode) context.getNewObject();
      
      Diagram targetDiagram = (Diagram) context.getTargetContainer();
      IPeCreateService peCreateService = Graphiti.getPeCreateService();
      // Create main container shape
      ContainerShape nodeContainer = peCreateService.createContainerShape(targetDiagram, true);
      
      // define a default size for the shape
      // check whether the context has a size (e.g. from a create feature)
      // otherwise define a default size for the shape
      IGaService gaService = Graphiti.getGaService();
      
      // create and set graphics algorithm
      ISEAnnotation[] annotations = addedNode.computeUsedAnnotations();
      RoundedRectangle roundedRectangle = gaService.createRoundedRectangle(nodeContainer, 20, 20);
      roundedRectangle.setStyle(ExecutionTreeStyleUtil.getStyleForDebugNode(annotations, getDiagram()));

      // create link and wire it
      link(nodeContainer, addedNode);

      // create shape for image
      Shape imageShape = peCreateService.createShape(nodeContainer, false);

      // create and set image graphics algorithm
      int dummyHeight = 20; // Real height is defined via layout feature
      Image image = gaService.createImage(imageShape, getImageId(addedNode));
      gaService.setLocationAndSize(image, MARGIN, 0, IMAGE_WIDTH, dummyHeight);
      
      // create link and wire it
      link(imageShape, addedNode);
      
      // create shape for text
      Shape textShape = peCreateService.createShape(nodeContainer, false);
      
      Text text = gaService.createDefaultText(getDiagram(), textShape);
      try {
         text.setValue(addedNode.getName());
      }
      catch (DebugException e) {
         text.setValue(e.getMessage());
      }
      text.setStyle(ExecutionTreeStyleUtil.getStyleForDebugNodeText(annotations, getDiagram()));
      text.setHorizontalAlignment(Orientation.ALIGNMENT_LEFT);
      text.setVerticalAlignment(Orientation.ALIGNMENT_CENTER);
      int dummyWidth = 100; // Real width is defined via layout feature
      gaService.setLocationAndSize(text, MARGIN + IMAGE_WIDTH + MARGIN, 0, dummyWidth, dummyHeight);
      // create link and wire it
      link(textShape, addedNode);

      int width = context.getWidth() <= 0 ? computeInitialWidth(targetDiagram, text.getValue(), text.getFont()) : context.getWidth();
      int height = context.getHeight() <= 0 ? computeInitialHeight(targetDiagram, text.getValue(), text.getFont()) : context.getHeight();
      gaService.setLocationAndSize(roundedRectangle, context.getX(), context.getY(), width, height);

      try
      {
         ChopboxAnchor anchor = peCreateService.createChopboxAnchor(nodeContainer);
         
         ISENode parentNode = NodeUtil.getParent(addedNode);

         if(parentNode != null)
         {
            // Since the first pe of a group startnode is always the rec
            // we need to get the second pe.
            PictogramElement pe = getFeatureProvider().getAllPictogramElementsForBusinessObject(parentNode)
                  [groupingSupported && NodeUtil.canBeGrouped(parentNode) ? 1 : 0];
               
            if (pe == null) {
               throw new DebugException(LogUtil.getLogger().createErrorStatus("Can't find PictogramElement for \"" + pe + "\"."));
            }
            
            if (!(pe instanceof AnchorContainer)) {
               throw new DebugException(LogUtil.getLogger().createErrorStatus("Parent PictogramElement \"" + pe + "\" is no AnchorContainer."));
            }
            AnchorContainer anchorContainer = (AnchorContainer)pe;
            if (anchorContainer.getAnchors() == null || anchorContainer.getAnchors().isEmpty()) {
               throw new DebugException(LogUtil.getLogger().createErrorStatus("Parent AnchorContainer \"" + pe + "\" has no Anchors."));
            }
            Connection connection = peCreateService.createFreeFormConnection(getDiagram());
            connection.setStart(anchorContainer.getAnchors().get(0));
            connection.setEnd(anchor);
            
            ConnectionDecorator cd = peCreateService.createConnectionDecorator(connection, false, 1.0, true);
            createArrow(gaService, cd);
     
            Polyline polyline = gaService.createPolyline(connection);
            polyline.setStyle(ExecutionTreeStyleUtil.getStyleForParentConnection(getDiagram()));
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
      }
      // call the layout feature to compute real heights and widths
      layoutPictogramElement(nodeContainer);

      return nodeContainer;
   }
   
   /**
    * Creates an arrow used in {@link ConnectionDecorator}s.
    * @param gaService The {@link IGaService} to use.
    * @param gaContainer The {@link GraphicsAlgorithmContainer} to use.
    * @return The created arrow {@link Polyline}.
    */
   protected Polyline createArrow(IGaService gaService, GraphicsAlgorithmContainer gaContainer) {
      Polyline polyline = gaService.createPolyline(gaContainer, new int[] {-10, 5, 0, 0, -10, -5});
      polyline.setStyle(ExecutionTreeStyleUtil.getStyleForParentConnection(getDiagram()));
      return polyline;
   }

   /**
    * Returns the image ID to use.
    * @param The {@link ISENode} to get the image for.
    * @return The image ID to use.
    */
   protected abstract String getImageId(ISENode node);

   /**
    * Computes the initial height for a node with the given text.
    * @param targetDiagram The target {@link Diagram}.
    * @param text The text in the node.
    * @param font The font of the text in the node.
    * @return The initial height to use.
    */
   public static int computeInitialHeight(Diagram targetDiagram, String text, Font font) {
      int minHeight = computeMinHeight(targetDiagram);
      IDimension textSize = GraphitiUtil.calculateTextSize(text != null ? text : StringUtil.EMPTY_STRING, font);
      if (textSize.getHeight() < minHeight) {
         return minHeight;
      }
      else {
         return GraphitiUtil.nextGrid(targetDiagram, textSize.getHeight());
      }
   }

   /**
    * Computes the initial width for a node with the given text.
    * @param targetDiagram The target {@link Diagram}.
    * @param text The text in the node.
    * @param font The font of the text in the node.
    * @return The initial width to use.
    */
   public static int computeInitialWidth(Diagram targetDiagram, String text, Font font) {
      int minWidth = computeMinWidth(targetDiagram);
      IDimension textSize = GraphitiUtil.calculateTextSize(text != null ? text : StringUtil.EMPTY_STRING, font);
      textSize.setWidth(textSize.getWidth() + MARGIN + IMAGE_WIDTH + MARGIN + MARGIN);
      if (textSize.getWidth() < minWidth) {
         return minWidth;
      }
      else {
         return GraphitiUtil.nextGrid(targetDiagram, textSize.getWidth());
      }
   }
   
   /**
    * Computes the minimal height.
    * @param targetDiagram The target {@link Diagram}.
    * @return The minimal height.
    */
   public static int computeMinHeight(Diagram targetDiagram) {
      return GraphitiUtil.nextGrid(targetDiagram, 20);
   }

   /**
    * Computes the minimal width.
    * @param targetDiagram The target {@link Diagram}.
    * @return The minimal width.
    */
   public static int computeMinWidth(Diagram targetDiagram) {
      return GraphitiUtil.nextGrid(targetDiagram, 50);
   }
}