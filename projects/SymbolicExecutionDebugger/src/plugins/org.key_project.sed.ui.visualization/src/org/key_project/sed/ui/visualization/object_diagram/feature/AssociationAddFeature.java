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

package org.key_project.sed.ui.visualization.object_diagram.feature;

import org.eclipse.graphiti.datatypes.IDimension;
import org.eclipse.graphiti.datatypes.ILocation;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.IAddConnectionContext;
import org.eclipse.graphiti.features.context.IAddContext;
import org.eclipse.graphiti.features.impl.AbstractAddFeature;
import org.eclipse.graphiti.mm.GraphicsAlgorithmContainer;
import org.eclipse.graphiti.mm.algorithms.Polyline;
import org.eclipse.graphiti.mm.algorithms.Rectangle;
import org.eclipse.graphiti.mm.algorithms.Text;
import org.eclipse.graphiti.mm.algorithms.styles.Orientation;
import org.eclipse.graphiti.mm.pictograms.ChopboxAnchor;
import org.eclipse.graphiti.mm.pictograms.Connection;
import org.eclipse.graphiti.mm.pictograms.ConnectionDecorator;
import org.eclipse.graphiti.mm.pictograms.ContainerShape;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.eclipse.graphiti.services.IPeCreateService;
import org.key_project.sed.ui.visualization.model.od.ODAssociation;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramStyleUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;

/**
 * Implementation of {@link IAddFeature} for {@link ODAssociation}s.
 * @author Martin Hentschel
 */
public class AssociationAddFeature extends AbstractAddFeature {
   /**
    * The margin used in the text label.
    */
   public static final int LABEL_MARGIN = 5;

   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public AssociationAddFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canAdd(IAddContext context) {
      // return true if given business object is an EReference
      // note, that the context must be an instance of IAddConnectionContext
      if (context instanceof IAddConnectionContext && context.getNewObject() instanceof ODAssociation) {
         return true;
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
      IAddConnectionContext addConContext = (IAddConnectionContext) context;
      ODAssociation addedAssociation = (ODAssociation)context.getNewObject();
      IPeCreateService peCreateService = Graphiti.getPeCreateService();
      IGaService gaService = Graphiti.getGaService();

      ContainerShape containerShape = peCreateService.createContainerShape(getDiagram(), true);
      // create and set graphics algorithm
      Rectangle rectangle = gaService.createRectangle(containerShape);
      rectangle.setStyle(ObjectDiagramStyleUtil.getStyleForAssociation(getDiagram()));
      Text text = gaService.createDefaultText(getDiagram(), rectangle, addedAssociation.getName());
      text.setHorizontalAlignment(Orientation.ALIGNMENT_CENTER);
      text.setStyle(ObjectDiagramStyleUtil.getStyleForAssociationText(getDiagram()));
      IDimension textDimension = GraphitiUtil.calculateTextSize(text.getValue(), gaService.getFont(text, true));
      gaService.setLocationAndSize(text, 0, 0, LABEL_MARGIN + textDimension.getWidth() + LABEL_MARGIN, textDimension.getHeight());
      // center rectangle in the middle of start and end anchor
      gaService.setSize(rectangle, text.getWidth(), text.getHeight());
      ILocation startLocation = GraphitiUtil.getCenterLocation(addConContext.getSourceAnchor());
      ILocation endLocation = GraphitiUtil.getCenterLocation(addConContext.getTargetAnchor());
      ILocation centeredLocation =  GraphitiUtil.center(startLocation, rectangle, endLocation);
      gaService.setLocation(rectangle, centeredLocation.getX(), centeredLocation.getY());
      // create link and wire it
      link(containerShape, addedAssociation);
      ChopboxAnchor containerAnchor = peCreateService.createChopboxAnchor(containerShape);
      
      
      // START CONNECTION WITH POLYLINE
      Connection startConnection = peCreateService.createFreeFormConnection(getDiagram());
      startConnection.setStart(addConContext.getSourceAnchor());
      startConnection.setEnd(containerAnchor);

      Polyline startPolyline = gaService.createPolyline(startConnection);
      startPolyline.setStyle(ObjectDiagramStyleUtil.getStyleForAssociation(getDiagram()));

      // create link and wire it
      link(startConnection, addedAssociation);
      
      
      // END CONNECTION WITH POLYLINE
      Connection endConnection = peCreateService.createFreeFormConnection(getDiagram());
      endConnection.setStart(containerAnchor);
      endConnection.setEnd(addConContext.getTargetAnchor());

      Polyline endPolyline = gaService.createPolyline(endConnection);
      endPolyline.setStyle(ObjectDiagramStyleUtil.getStyleForAssociation(getDiagram()));

      // create link and wire it
      link(endConnection, addedAssociation);
      
      // add static graphical decorator (composition and navigable)
      ConnectionDecorator cd = peCreateService.createConnectionDecorator(endConnection, false, 1.0, true);
      createArrow(cd);
      
      return null;
   }
   
   /**
    * Creates an arrow used in {@link ConnectionDecorator}s.
    * @param gaService The {@link IGaService} to use.
    * @param gaContainer The {@link GraphicsAlgorithmContainer} to use.
    * @return The created arrow {@link Polyline}.
    */
   protected Polyline createArrow(GraphicsAlgorithmContainer gaContainer) {
      IGaService gaService = Graphiti.getGaService();
      Polyline polyline = gaService.createPolyline(gaContainer, new int[] {-10, 5, 0, 0, -10, -5});
      polyline.setStyle(ObjectDiagramStyleUtil.getStyleForAssociation(getDiagram()));
      return polyline;
   }
}