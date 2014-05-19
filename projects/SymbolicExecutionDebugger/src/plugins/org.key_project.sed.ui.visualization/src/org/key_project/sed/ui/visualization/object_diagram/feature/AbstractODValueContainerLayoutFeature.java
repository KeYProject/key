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

import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.graphiti.datatypes.IDimension;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.ILayoutFeature;
import org.eclipse.graphiti.features.context.ILayoutContext;
import org.eclipse.graphiti.features.impl.AbstractLayoutFeature;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.algorithms.Polyline;
import org.eclipse.graphiti.mm.algorithms.styles.Point;
import org.eclipse.graphiti.mm.pictograms.ContainerShape;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.mm.pictograms.Shape;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer;
import org.key_project.sed.ui.visualization.model.od.ODObject;
import org.key_project.sed.ui.visualization.model.od.ODValue;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramUtil;

/**
 * Provides a basic implementation of {@link ILayoutFeature} for {@link AbstractODValueContainer}s.
 * @author Martin Hentschel
 */
public abstract class AbstractODValueContainerLayoutFeature extends AbstractLayoutFeature {
   /**
    * The minimal width of the graphical representation of an {@link ODObject}.
    */
   public static final int MIN_WIDTH = 50;

   /**
    * The minimal height of the graphical representation of an {@link ODObject}.
    */
   public static final int MIN_HEIGHT = 50;

   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link ILayoutFeature}.
    */
   public AbstractODValueContainerLayoutFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canLayout(ILayoutContext context) {
      // return true, if pictogram element is linked to an supported business object
      PictogramElement pe = context.getPictogramElement();
      if (!(pe instanceof ContainerShape))
         return false;
      EList<EObject> businessObjects = pe.getLink().getBusinessObjects();
      return businessObjects.size() == 1 && isBusinessObjectSupported(businessObjects.get(0));
   }
   
   /**
    * Checks if the given business object is supported by this feature.
    * @param bo The business object to check for support.
    * @return {@code true} is supported, {@code false} is not supported.
    */
   protected abstract boolean isBusinessObjectSupported(Object bo);

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean layout(ILayoutContext context) {
      boolean anythingChanged = false;
      ContainerShape containerShape = (ContainerShape) context.getPictogramElement();
      GraphicsAlgorithm containerGa = containerShape.getGraphicsAlgorithm();

      // height
      if (containerGa.getHeight() < MIN_HEIGHT) {
         containerGa.setHeight(MIN_HEIGHT);
         anythingChanged = true;
      }

      // width
      if (containerGa.getWidth() < MIN_WIDTH) {
         containerGa.setWidth(MIN_WIDTH);
         anythingChanged = true;
      }

      int containerWidth = containerGa.getWidth();

      for (Shape shape : containerShape.getChildren()) {
         GraphicsAlgorithm graphicsAlgorithm = shape.getGraphicsAlgorithm();
         IGaService gaService = Graphiti.getGaService();
         IDimension size = gaService.calculateSize(graphicsAlgorithm);
         if (containerWidth != size.getWidth()) {
            if (graphicsAlgorithm instanceof Polyline) {
               Polyline polyline = (Polyline) graphicsAlgorithm;
               Point secondPoint = polyline.getPoints().get(1);
               Point newSecondPoint = gaService.createPoint(containerWidth, secondPoint.getY());
               polyline.getPoints().set(1, newSecondPoint);
               anythingChanged = true;
            }
            else {
               Object bo = getBusinessObjectForPictogramElement(graphicsAlgorithm.getPictogramElement());
               if (bo instanceof ODValue) {
                  gaService.setWidth(graphicsAlgorithm, containerWidth - (2 * ObjectDiagramUtil.HORIZONTAL_OFFSET));
               }
               else {
                  gaService.setWidth(graphicsAlgorithm, containerWidth);
               }
               anythingChanged = true;
            }
         }
      }
      return anythingChanged;
   }
}