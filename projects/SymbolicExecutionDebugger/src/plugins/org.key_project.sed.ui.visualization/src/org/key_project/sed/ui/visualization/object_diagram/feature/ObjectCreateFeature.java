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

import org.eclipse.graphiti.features.ICreateFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICreateContext;
import org.eclipse.graphiti.features.impl.AbstractCreateFeature;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.key_project.sed.ui.visualization.model.od.ODObject;
import org.key_project.sed.ui.visualization.object_diagram.provider.IObjectDiagramImageConstants;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramUtil;
import org.key_project.sed.ui.visualization.object_diagram.wizard.CreateObjectWizard;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * Implementation of {@link ICreateFeature} for {@link ODObject}s.
 * @author Martin Hentschel
 */
public class ObjectCreateFeature extends AbstractCreateFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link ICreateFeature}.
    */
   public ObjectCreateFeature(IFeatureProvider fp) {
      super(fp, "Object", "Create Object");
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getCreateImageId() {
      return IObjectDiagramImageConstants.IMG_OBJECT;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canCreate(ICreateContext context) {
      return context.getTargetContainer() instanceof Diagram;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Object[] create(ICreateContext context) {
      // Create new object 
      ODObject object = CreateObjectWizard.openWizard(WorkbenchUtil.getActiveShell());
      if (object == null) {
         return EMPTY;
      }
      else {
         // Add model element to resource of the diagram.
         ObjectDiagramUtil.getModel(getDiagram()).getObjects().add(object);
         // Do the add
         addGraphicalRepresentation(context, object);
         // Return newly created business object(s)
         return new Object[] { object };
      }
   }
}