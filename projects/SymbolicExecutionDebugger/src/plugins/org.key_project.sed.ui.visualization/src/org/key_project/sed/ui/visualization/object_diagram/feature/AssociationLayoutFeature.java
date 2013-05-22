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

import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.ILayoutFeature;
import org.eclipse.graphiti.features.context.ILayoutContext;
import org.eclipse.graphiti.features.impl.AbstractLayoutFeature;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.pictograms.ContainerShape;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.key_project.sed.ui.visualization.model.od.ODAssociation;

/**
 * Implementation of {@link ILayoutFeature} for {@link ODAssociation}s.
 * @author Martin Hentschel
 */
public class AssociationLayoutFeature extends AbstractLayoutFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link ILayoutFeature}.
    */
   public AssociationLayoutFeature(IFeatureProvider fp) {
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
      return businessObjects.size() == 1 && businessObjects.get(0) instanceof ODAssociation;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean layout(ILayoutContext context) {
      boolean anythingChanged = false;
      ContainerShape containerShape = (ContainerShape) context.getPictogramElement();
      GraphicsAlgorithm containerGa = containerShape.getGraphicsAlgorithm();
      if (containerGa != null) {
         for (GraphicsAlgorithm child : containerGa.getGraphicsAlgorithmChildren()) {
            child.setWidth(containerGa.getWidth());
            child.setHeight(containerGa.getHeight());
            anythingChanged = true;
         }
      }
      return anythingChanged;
   }
}