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

import org.eclipse.emf.ecore.EObject;
import org.eclipse.graphiti.features.ICreateFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICreateContext;
import org.eclipse.graphiti.features.impl.AbstractCreateFeature;
import org.eclipse.graphiti.mm.pictograms.ContainerShape;
import org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer;
import org.key_project.sed.ui.visualization.model.od.ODValue;
import org.key_project.sed.ui.visualization.object_diagram.provider.IObjectDiagramImageConstants;
import org.key_project.sed.ui.visualization.object_diagram.wizard.CreateValueWizard;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * Implementation of {@link ICreateFeature} for {@link ODValue}s.
 * @author Martin Hentschel
 */
public class ValueCreateFeature extends AbstractCreateFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link ICreateFeature}.
    */
   public ValueCreateFeature(IFeatureProvider fp) {
      super(fp, "Value", "Create Value");
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getCreateImageId() {
      return IObjectDiagramImageConstants.IMG_VALUE;
   }


   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canCreate(ICreateContext context) {
      ContainerShape targetContainer = context.getTargetContainer();
      if (targetContainer != null) {
         return findValueContainer(targetContainer) != null;
      }
      else {
         return false;
      }
   }
   
   /**
    * Searches the first {@link AbstractODValueContainer} in the containment
    * hierarchy of the business {@link EObject}s starting at the business object
    * of the given {@link ContainerShape}.
    * @param targetContainer The starting point.
    * @return The found {@link AbstractODValueContainer} or {@code null} if no one was found.
    */
   protected AbstractODValueContainer findValueContainer(ContainerShape targetContainer) {
      AbstractODValueContainer result = null;
      if (targetContainer != null) {
         Object bo = getBusinessObjectForPictogramElement(targetContainer);
         if (bo instanceof EObject) {
            EObject ebo = (EObject)bo;
            while (result == null && ebo != null) {
               if (ebo instanceof AbstractODValueContainer) {
                  result = (AbstractODValueContainer)ebo;
               }
               else {
                  ebo = ebo.eContainer();
               }
            }
         }
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Object[] create(ICreateContext context) {
      // Create new value 
      ODValue value = CreateValueWizard.openWizard(WorkbenchUtil.getActiveShell());
      if (value == null) {
         return EMPTY;
      }
      else {
         // Add model element to resource of the diagram.
         AbstractODValueContainer bo = findValueContainer(context.getTargetContainer());
         bo.getValues().add(value);
         // Do the add
         addGraphicalRepresentation(context, value);
         // Return newly created business object(s)
         return new Object[] { value };
      }
   }
}