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

import org.eclipse.graphiti.features.ICreateFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICreateConnectionContext;
import org.eclipse.graphiti.features.context.impl.AddConnectionContext;
import org.eclipse.graphiti.features.impl.AbstractCreateConnectionFeature;
import org.eclipse.graphiti.mm.pictograms.Connection;
import org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer;
import org.key_project.sed.ui.visualization.model.od.ODAssociation;
import org.key_project.sed.ui.visualization.model.od.ODObject;
import org.key_project.sed.ui.visualization.object_diagram.provider.IObjectDiagramImageConstants;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramUtil;
import org.key_project.sed.ui.visualization.object_diagram.wizard.CreateAssociationWizard;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * Implementation of {@link ICreateFeature} for {@link ODAssociation}s.
 * @author Martin Hentschel
 */
public class AssociationCreateFeature extends AbstractCreateConnectionFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link ICreateFeature}.
    */
   public AssociationCreateFeature(IFeatureProvider fp) {
      super(fp, "Association", "Create Association");
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getCreateImageId() {
      return IObjectDiagramImageConstants.IMG_ASSOCIATION;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canStartConnection(ICreateConnectionContext context) {
      AbstractODValueContainer source = ObjectDiagramUtil.getValueContainer(getFeatureProvider(), context.getSourceAnchor());
      return source != null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canCreate(ICreateConnectionContext context) {
      AbstractODValueContainer source = ObjectDiagramUtil.getValueContainer(getFeatureProvider(), context.getSourceAnchor());
      ODObject target = ObjectDiagramUtil.getObject(getFeatureProvider(), context.getTargetAnchor());
      return source != null && target != null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Connection create(ICreateConnectionContext context) {
      // create new business object
      ODAssociation association = CreateAssociationWizard.openWizard(WorkbenchUtil.getActiveShell());
      if (association != null) {
         Connection newConnection = null;

         // get ODObject which should be connected
         AbstractODValueContainer source = ObjectDiagramUtil.getValueContainer(getFeatureProvider(), context.getSourceAnchor());
         ODObject target = ObjectDiagramUtil.getObject(getFeatureProvider(), context.getTargetAnchor());
         
         if (source != null && target != null) {
            // Add new association to business model
            association.setTarget(target);
            source.getAssociations().add(association);
            // add connection for business object
            AddConnectionContext addContext = new AddConnectionContext(context.getSourceAnchor(), context.getTargetAnchor());
            addContext.setNewObject(association);
            newConnection = (Connection)getFeatureProvider().addIfPossible(addContext);
         }

         return newConnection;
      }
      else {
         return null;
      }
   }
}