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

import org.eclipse.graphiti.datatypes.IDimension;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.IAddContext;
import org.eclipse.graphiti.features.context.impl.AddContext;
import org.eclipse.graphiti.features.context.impl.AreaContext;
import org.eclipse.graphiti.features.impl.AbstractAddShapeFeature;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.algorithms.Polyline;
import org.eclipse.graphiti.mm.algorithms.Text;
import org.eclipse.graphiti.mm.algorithms.styles.Orientation;
import org.eclipse.graphiti.mm.pictograms.ContainerShape;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.mm.pictograms.Shape;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.eclipse.graphiti.services.IPeCreateService;
import org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer;
import org.key_project.sed.ui.visualization.model.od.ODValue;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramStyleUtil;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;

/**
 * Provides a basic implementation of {@link IAddFeature} for {@link AbstractODValueContainer}s.
 * @author Martin Hentschel
 */
public abstract class AbstractODValueContainerAddFeature<T extends AbstractODValueContainer> extends AbstractAddShapeFeature {
   /**
    * Property for an {@link Boolean} instance which indicates
    * to update the size of the new created {@link PictogramElement}.
    */
   public static final String PROPERTY_UPDATE_SIZE = "updateSize";
   
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public AbstractODValueContainerAddFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canAdd(IAddContext context) {
      // check if user wants to add a EClass
      if (isNewObjectSupported(context.getNewObject())) {
         // check if user wants to add to a diagram
         if (context.getTargetContainer() instanceof Diagram) {
            return true;
         }
      }
      return false;
   }
   
   /**
    * Checks if the given new object is supported by this feature.
    * @param newObject The new object to check for support.
    * @return {@code true} is supported, {@code false} is not supported.
    */
   protected abstract boolean isNewObjectSupported(Object newObject);

   /**
    * {@inheritDoc}
    */
   @Override
   public PictogramElement add(IAddContext context) {
      @SuppressWarnings("unchecked")
      T addedObject = (T)context.getNewObject();
      ContainerShape targetContainer = context.getTargetContainer();
      boolean updateSize = Boolean.TRUE.equals(context.getProperty(PROPERTY_UPDATE_SIZE));
      
      // CONTAINER SHAPE WITH ROUNDED RECTANGLE
      IPeCreateService peCreateService = Graphiti.getPeCreateService();
      ContainerShape containerShape = peCreateService.createContainerShape(targetContainer, true);

      // check whether the context has a size (e.g. from a create feature)
      // otherwise define a default size for the shape
      final int width = context.getWidth() < ObjectLayoutFeature.MIN_WIDTH ? ObjectLayoutFeature.MIN_WIDTH : context.getWidth();
      final int height = context.getHeight() < ObjectLayoutFeature.MIN_HEIGHT ? ObjectLayoutFeature.MIN_HEIGHT : context.getHeight();
      IGaService gaService = Graphiti.getGaService();

      // create and set graphics algorithm
      GraphicsAlgorithm roundedRectangle = createOuterBorder(gaService, containerShape);
      roundedRectangle.setStyle(ObjectDiagramStyleUtil.getStyleForObject(getDiagram()));
      gaService.setLocationAndSize(roundedRectangle, context.getX(), context.getY(), width, height);
      // create link and wire it
      link(containerShape, addedObject);

      // create shape for text
      Shape textShape = peCreateService.createShape(containerShape, false);
      // create and set text graphics algorithm
      Text text = gaService.createText(textShape, computeName(addedObject));
      text.setStyle(ObjectDiagramStyleUtil.getStyleForObjectText(getDiagram()));
      text.setHorizontalAlignment(Orientation.ALIGNMENT_CENTER);
      // Compute text height
      IDimension textDimension = GraphitiUtil.calculateTextSize(text.getValue(), gaService.getFont(text, true));
      int textHeight = textDimension != null ? textDimension.getHeight() : 20;
      int optimalWidth = textDimension != null ? ObjectDiagramUtil.VERTICAL_OFFSET + textDimension.getWidth() + ObjectDiagramUtil.VERTICAL_OFFSET : width;
      // vertical alignment has as default value "center"
      gaService.setLocationAndSize(text, 0, ObjectDiagramUtil.VERTICAL_OFFSET, width, textHeight);
      // create link and wire it
      link(textShape, addedObject);

      // create shape for line
      Shape polylineShape = peCreateService.createShape(containerShape, false);
      // create and set graphics algorithm
      Polyline polyline = gaService.createPolyline(polylineShape, new int[] { 0, 0, width, 0 });
      polyline.setStyle(ObjectDiagramStyleUtil.getStyleForObject(getDiagram()));
      gaService.setLocationAndSize(polyline, 0, textHeight + (2 * ObjectDiagramUtil.VERTICAL_OFFSET), width, polyline.getLineWidth());
      
      // add a chopbox anchor to the shape 
      peCreateService.createChopboxAnchor(containerShape);
      
      // add values
      int optimalHeight = 0;
      for (ODValue value : addedObject.getValues()) {
         AddContext valueContext = new AddContext(new AreaContext(), value);
         valueContext.setTargetContainer(containerShape);
         PictogramElement valuePE = addGraphicalRepresentation(valueContext, value);
         if (valuePE.getGraphicsAlgorithm() instanceof Text) {
            Text valueText = (Text)valuePE.getGraphicsAlgorithm();
            IDimension valueTextDimension = GraphitiUtil.calculateTextSize(valueText.getValue(), gaService.getFont(valueText, true));
            if (valueTextDimension != null) {
               int optimalValueWidth = ObjectDiagramUtil.HORIZONTAL_OFFSET + valueTextDimension.getWidth() + ObjectDiagramUtil.HORIZONTAL_OFFSET;
               if (optimalValueWidth > optimalWidth) {
                  optimalWidth = optimalValueWidth;
               }
            }
            int maxValueY = valueText.getY() + valueText.getHeight() + ObjectDiagramUtil.HORIZONTAL_OFFSET;
            if (maxValueY > optimalHeight) {
               optimalHeight = maxValueY;
            }
         }
      }

      // update size to optimal size if requested
      if (updateSize) {
         containerShape.getGraphicsAlgorithm().setWidth(optimalWidth);
         containerShape.getGraphicsAlgorithm().setHeight(optimalHeight < ObjectLayoutFeature.MIN_HEIGHT ? ObjectLayoutFeature.MIN_HEIGHT : optimalHeight);
      }
      
      // call the layout feature
      layoutPictogramElement(containerShape);

      return containerShape;
   }
   
   /**
    * Creates the outer border.
    * @param gaService The {@link IGaService} to use.
    * @param containerShape The parent {@link ContainerShape}.
    * @return The created outer border.
    */
   protected abstract GraphicsAlgorithm createOuterBorder(IGaService gaService, ContainerShape containerShape);

   /**
    * Computes the name to show.
    * @param addedObject The added object.
    * @return The name to show.
    */
   protected String computeName(T addedObject) {
      return addedObject.getName();
   }
}