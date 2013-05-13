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

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.graphiti.datatypes.ILocation;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.impl.AddConnectionContext;
import org.eclipse.graphiti.features.context.impl.AddContext;
import org.eclipse.graphiti.features.context.impl.AreaContext;
import org.eclipse.graphiti.features.custom.AbstractCustomFeature;
import org.eclipse.graphiti.features.custom.ICustomFeature;
import org.eclipse.graphiti.mm.algorithms.styles.Point;
import org.eclipse.graphiti.mm.pictograms.Anchor;
import org.eclipse.graphiti.mm.pictograms.AnchorContainer;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.mm.pictograms.FreeFormConnection;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.services.Graphiti;
import org.key_project.sed.ui.visualization.model.od.ODAssociation;
import org.key_project.sed.ui.visualization.model.od.ODModel;
import org.key_project.sed.ui.visualization.model.od.ODObject;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.util.java.CollectionUtil;

/**
 * Provides the basic functionality to generate object diagrams.
 * @author Martin Hentschel
 */
public abstract class AbstractGenerateObjectDiagramCustomFeature extends AbstractCustomFeature {
   /**
    * The horizontal distance between {@link ODObject} in a diagram.
    */
   public static final int HORIZONTAL_OFFSET_BETWEEN_OBJECTS = 50;

   /**
    * The vertical distance between {@link ODObject} in a diagram.
    */
   public static final int VERTICAL_OFFSET_BETWEEN_OBJECTS = 50;

   /**
    * Offset for bend points.
    */
   public static final int BEND_POINT_OFFSET = 20;

   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link ICustomFeature}.
    */
   public AbstractGenerateObjectDiagramCustomFeature(IFeatureProvider fp) {
      super(fp);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canExecute(ICustomContext context) {
      return true;
   }
   
   /**
    * Adds the given business object as new node to the diagram ({@link #getDiagram()}).
    * @param bo The business object to add.
    * @param x The x coordinate.
    * @param y The y coordinate.
    * @return The created {@link PictogramElement}.
    */
   protected PictogramElement addNodeToDiagram(Object bo, int x, int y) {
      AddContext context = new AddContext(new AreaContext(), bo);
      context.setTargetContainer(getDiagram());
      context.setLocation(x, y);
      context.putProperty(AbstractODValueContainerAddFeature.PROPERTY_UPDATE_SIZE, Boolean.TRUE);
      return getFeatureProvider().addIfPossible(context);
   }
   
   /**
    * Adds the given business object as new connection to the diagram ({@link #getDiagram()}).
    * @param bo The business object to add.
    * @param source The source {@link PictogramElement} which must be an instance of {@link AnchorContainer}.
    * @param target The target {@link PictogramElement} which must be an instance of {@link AnchorContainer}.
    * @return The created {@link PictogramElement}.
    */
   protected PictogramElement addConnectionToDiagram(Object bo, PictogramElement source, PictogramElement target) {
      Assert.isTrue(source instanceof AnchorContainer);
      Assert.isTrue(target instanceof AnchorContainer);
      Anchor sourceAnchor = CollectionUtil.getFirst(((AnchorContainer)source).getAnchors());
      Anchor targetAnchor = CollectionUtil.getFirst(((AnchorContainer)target).getAnchors());
      AddConnectionContext context = new AddConnectionContext(sourceAnchor, targetAnchor);
      context.setNewObject(bo);
      return getFeatureProvider().addIfPossible(context);
   }

   /**
    * Improves the layout of the {@link Diagram}.
    * @param model The {@link ODModel}.
    * @param monitor The {@link IProgressMonitor} to use.
    */
   protected void improveLayout(ODModel model, IProgressMonitor monitor) {
      // Execute layouter
      GraphitiUtil.layoutTopLevelElements(getFeatureProvider(), getDiagram(), 30, true, false, monitor);
      // Improve self connections
      for (ODObject object : model.getObjects()) {
         for (ODAssociation association : object.getAssociations()) {
            if (object == association.getTarget()) {
               improveSelfAssociation(association);
            }
         }
      }
   }
   
   /**
    * Improves self associations (source == target) by adding bend points
    * because otherwise the connection from source to label and label to target
    * is located exactly on each other.
    * @param association The self {@link ODAssociation} to improve.
    */
   protected void improveSelfAssociation(ODAssociation association) {
      PictogramElement[] pes = getFeatureProvider().getAllPictogramElementsForBusinessObject(association);
      boolean odd = true;
      for (PictogramElement pe : pes) {
         if (pe instanceof FreeFormConnection) {
            FreeFormConnection ffc = (FreeFormConnection)pe;
            if (ffc.getBendpoints().isEmpty()) {
               ILocation start = GraphitiUtil.getRightLocation(ffc.getStart());
               ILocation end = GraphitiUtil.getLeftLocation(ffc.getEnd());
               if (start.getX() > end.getX()) {
                  start = GraphitiUtil.getLeftLocation(ffc.getStart());
                  end = GraphitiUtil.getRightLocation(ffc.getEnd());
               }
               ILocation centered = GraphitiUtil.center(start, end);
               int xOffset = start.getY() != end.getY() ? (odd ? BEND_POINT_OFFSET : -BEND_POINT_OFFSET) : 0;
               int yOffset = start.getX() != end.getX() ? (odd ? BEND_POINT_OFFSET : -BEND_POINT_OFFSET) : 0;
               Point bp = Graphiti.getGaCreateService().createPoint(centered.getX() + xOffset, 
                                                                    centered.getY() + yOffset);
               ffc.getBendpoints().add(bp);
               odd = !odd;
            }
         }
      }
   }

   /**
    * Removes all children from the given model and its {@link Diagram}.
    * @param model The {@link ODModel} to empty.
    */
   protected void cleanModel(ODModel model) {
      // Empty diagram
      PictogramElement[] pes = GraphitiUtil.getAllPictogramElements(getDiagram());
      for (PictogramElement pe : pes) {
         Graphiti.getPeService().deletePictogramElement(pe);
      }
      // Empty model
      model.getObjects().clear();
      model.getStates().clear();
   }
}