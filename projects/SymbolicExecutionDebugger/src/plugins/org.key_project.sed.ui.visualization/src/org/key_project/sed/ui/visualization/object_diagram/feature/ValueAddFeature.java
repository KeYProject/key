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

import org.eclipse.draw2d.CoordinateListener;
import org.eclipse.graphiti.datatypes.IDimension;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.IAddContext;
import org.eclipse.graphiti.features.impl.AbstractAddShapeFeature;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.algorithms.Text;
import org.eclipse.graphiti.mm.algorithms.styles.Orientation;
import org.eclipse.graphiti.mm.pictograms.ContainerShape;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.eclipse.graphiti.services.IPeCreateService;
import org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer;
import org.key_project.sed.ui.visualization.model.od.ODObject;
import org.key_project.sed.ui.visualization.model.od.ODValue;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramStyleUtil;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.util.java.StringUtil;

/**
 * Implementation of {@link IAddFeature} for {@link ODValue}s.
 * @author Martin Hentschel
 */
public class ValueAddFeature extends AbstractAddShapeFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public ValueAddFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canAdd(IAddContext context) {
      if (context.getNewObject() instanceof ODValue) {
         ODValue value = (ODValue)context.getNewObject();
         return value.eContainer() != null && 
                getFeatureProvider().getPictogramElementForBusinessObject(value.eContainer()) instanceof ContainerShape;
      }
      else {
         return false;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public PictogramElement add(IAddContext context) {
      ODValue addedValue = (ODValue)context.getNewObject();
      ContainerShape targetContainer = (ContainerShape)getFeatureProvider().getPictogramElementForBusinessObject(addedValue.eContainer());

      // CONTAINER SHAPE WITH ROUNDED RECTANGLE
      IPeCreateService peCreateService = Graphiti.getPeCreateService();
      ContainerShape containerShape = peCreateService.createContainerShape(targetContainer, true);

      // check whether the context has a size (e.g. from a create feature)
      // otherwise define a default size for the shape
      IGaService gaService = Graphiti.getGaService();

      // create and set text graphics algorithm
      Text text = gaService.createText(containerShape, addedValue.getName() + " = " + (addedValue.getValue() != null ? addedValue.getValue() : StringUtil.EMPTY_STRING));
      text.setStyle(ObjectDiagramStyleUtil.getStyleForValueText(getDiagram()));
      text.setHorizontalAlignment(Orientation.ALIGNMENT_LEFT);
      // vertical alignment has as default value "center"
      final int width = targetContainer.getGraphicsAlgorithm().getWidth() - (ObjectDiagramUtil.HORIZONTAL_OFFSET * 2);
      IDimension textDimension = GraphitiUtil.calculateTextSize(text.getValue(), gaService.getFont(text, true));
      final int height = textDimension != null ? textDimension.getHeight() : 20;
      gaService.setLocationAndSize(text, ObjectDiagramUtil.HORIZONTAL_OFFSET, getYForNewValue(targetContainer), width, height);

      // create link and wire it
      link(containerShape, addedValue);

      // call the layout feature
      layoutPictogramElement(containerShape);

      return containerShape;
   }
   
   /**
    * Computes the Y coordinate for new {@link ODValue}s in its
    * parent {@link ODObject} which is the Y coordinate and height of the
    * last shown {@link ODValue} or under the separator line if currently
    * no {@link ODValue} is shown.
    * @param targetContainer The {@link ContainerShape} of the {@link ODObject}.
    * @return The Y coordinate for a new {@link ODValue}.
    */
   protected int getYForNewValue(ContainerShape targetContainer) {
      AbstractODValueContainer object = (AbstractODValueContainer)getBusinessObjectForPictogramElement(targetContainer);
      int maxY = 0;
      boolean peFound = false;
      for (ODValue value : object.getValues()) {
         PictogramElement pe = getFeatureProvider().getPictogramElementForBusinessObject(value);
         if (pe != null) {
            peFound = true;
            int peY = pe.getGraphicsAlgorithm().getY() + pe.getGraphicsAlgorithm().getHeight();
            if (peY > maxY) {
               maxY = peY;
            }
         }
      }
      return peFound ? maxY : getYForFirstNewValue(targetContainer);
   }
   
   /**
    * Computes the Y {@link CoordinateListener} for the first {@link ODValue}
    * shown in its parent {@link ODObject} which is under the separator line.
    * @param targetContainer The {@link ContainerShape} of the {@link ODObject}.
    * @return The Y coordinate for a new {@link ODValue}.
    */
   protected int getYForFirstNewValue(ContainerShape targetContainer) {
      GraphicsAlgorithm x = targetContainer.getChildren().get(1).getGraphicsAlgorithm();
      return x.getY() + x.getHeight() + ObjectDiagramUtil.VERTICAL_OFFSET;
   }
}