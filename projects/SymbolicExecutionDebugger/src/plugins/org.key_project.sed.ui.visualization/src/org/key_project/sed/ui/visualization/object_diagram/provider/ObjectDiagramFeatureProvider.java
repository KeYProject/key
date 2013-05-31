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

package org.key_project.sed.ui.visualization.object_diagram.provider;

import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.ICreateConnectionFeature;
import org.eclipse.graphiti.features.ICreateFeature;
import org.eclipse.graphiti.features.IDeleteFeature;
import org.eclipse.graphiti.features.IDirectEditingFeature;
import org.eclipse.graphiti.features.IFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.ILayoutFeature;
import org.eclipse.graphiti.features.IMoveShapeFeature;
import org.eclipse.graphiti.features.IPasteFeature;
import org.eclipse.graphiti.features.IReconnectionFeature;
import org.eclipse.graphiti.features.IRemoveFeature;
import org.eclipse.graphiti.features.IResizeShapeFeature;
import org.eclipse.graphiti.features.IUpdateFeature;
import org.eclipse.graphiti.features.context.IAddContext;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.IDeleteContext;
import org.eclipse.graphiti.features.context.IDirectEditingContext;
import org.eclipse.graphiti.features.context.ILayoutContext;
import org.eclipse.graphiti.features.context.IMoveShapeContext;
import org.eclipse.graphiti.features.context.IPasteContext;
import org.eclipse.graphiti.features.context.IPictogramElementContext;
import org.eclipse.graphiti.features.context.IReconnectionContext;
import org.eclipse.graphiti.features.context.IRemoveContext;
import org.eclipse.graphiti.features.context.IResizeShapeContext;
import org.eclipse.graphiti.features.context.IUpdateContext;
import org.eclipse.graphiti.features.custom.ICustomFeature;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.ui.features.DefaultFeatureProvider;
import org.key_project.sed.ui.visualization.model.od.ODAssociation;
import org.key_project.sed.ui.visualization.model.od.ODObject;
import org.key_project.sed.ui.visualization.model.od.ODState;
import org.key_project.sed.ui.visualization.model.od.ODValue;
import org.key_project.sed.ui.visualization.object_diagram.feature.AssociationAddFeature;
import org.key_project.sed.ui.visualization.object_diagram.feature.AssociationCreateFeature;
import org.key_project.sed.ui.visualization.object_diagram.feature.AssociationLayoutFeature;
import org.key_project.sed.ui.visualization.object_diagram.feature.AssociationReconnectionFeature;
import org.key_project.sed.ui.visualization.object_diagram.feature.ObjectAddFeature;
import org.key_project.sed.ui.visualization.object_diagram.feature.ObjectCreateFeature;
import org.key_project.sed.ui.visualization.object_diagram.feature.ObjectLayoutFeature;
import org.key_project.sed.ui.visualization.object_diagram.feature.StateAddFeature;
import org.key_project.sed.ui.visualization.object_diagram.feature.StateCreateFeature;
import org.key_project.sed.ui.visualization.object_diagram.feature.StateLayoutFeature;
import org.key_project.sed.ui.visualization.object_diagram.feature.ValueAddFeature;
import org.key_project.sed.ui.visualization.object_diagram.feature.ValueCreateFeature;
import org.key_project.sed.ui.visualization.object_diagram.feature.ValueMoveFeature;
import org.key_project.sed.ui.visualization.object_diagram.feature.ValueResizeFeature;

/**
 * {@link IFeatureProvider} specific implementation for object diagrams.
 * @author Martin Hentschel
 */
public class ObjectDiagramFeatureProvider extends DefaultFeatureProvider {
   /**
    * Indicates that the diagram is read-only or editable.
    */
   private boolean readOnly = false;
   
   /**
    * Constructor.
    * @param dtp The diagram type provider for that this {@link IFeatureProvider} is used.
    */
   public ObjectDiagramFeatureProvider(IDiagramTypeProvider dtp) {
      super(dtp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ICreateFeature[] getCreateFeatures() {
      if (!isReadOnly()) {
         return new ICreateFeature[] { new StateCreateFeature(this),
               new ObjectCreateFeature(this),
               new ValueCreateFeature(this) };
      }
      else {
         return new ICreateFeature[0];
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IAddFeature getAddFeature(IAddContext context) {
      if (context.getNewObject() instanceof ODObject) {
         return new ObjectAddFeature(this);
      }
      else if (context.getNewObject() instanceof ODAssociation) {
         return new AssociationAddFeature(this);
      }
      else if (context.getNewObject() instanceof ODValue) {
         return new ValueAddFeature(this);
      }
      else if (context.getNewObject() instanceof ODState) {
         return new StateAddFeature(this);
      }
      else {
         return super.getAddFeature(context);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ILayoutFeature getLayoutFeature(ILayoutContext context) {
      PictogramElement pictogramElement = context.getPictogramElement();
      Object bo = getBusinessObjectForPictogramElement(pictogramElement);
      if (bo instanceof ODObject) {
         return new ObjectLayoutFeature(this);
      }
      else if (bo instanceof ODState) {
         return new StateLayoutFeature(this);
      }
      else if (bo instanceof ODAssociation) {
         return new AssociationLayoutFeature(this);
      }
      else {
         return super.getLayoutFeature(context);
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IMoveShapeFeature getMoveShapeFeature(IMoveShapeContext context) {
      PictogramElement pictogramElement = context.getPictogramElement();
      Object bo = getBusinessObjectForPictogramElement(pictogramElement);
      if (bo instanceof ODValue) {
         return new ValueMoveFeature(this);
      }
      else {
         return super.getMoveShapeFeature(context);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IResizeShapeFeature getResizeShapeFeature(IResizeShapeContext context) {
      PictogramElement pictogramElement = context.getPictogramElement();
      Object bo = getBusinessObjectForPictogramElement(pictogramElement);
      if (bo instanceof ODValue) {
         return new ValueResizeFeature(this);
      }
      else {
         return super.getResizeShapeFeature(context);
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public ICreateConnectionFeature[] getCreateConnectionFeatures() {
      if (!isReadOnly()) {
         return new ICreateConnectionFeature[] { new AssociationCreateFeature(this) };
      }
      else {
         return new ICreateConnectionFeature[0];
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IReconnectionFeature getReconnectionFeature(IReconnectionContext context) {
       return new AssociationReconnectionFeature(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDeleteFeature getDeleteFeature(IDeleteContext context) {
      if (!isReadOnly()) {
         return super.getDeleteFeature(context);
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IRemoveFeature getRemoveFeature(IRemoveContext context) {
      if (!isReadOnly()) {
         return super.getRemoveFeature(context);
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IUpdateFeature getUpdateFeature(IUpdateContext context) {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ICustomFeature[] getCustomFeatures(ICustomContext context) {
      if (!isReadOnly()) {
         return super.getCustomFeatures(context);
      }
      else {
         return new ICustomFeature[0];
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IPasteFeature getPasteFeature(IPasteContext context) {
      if (!isReadOnly()) {
         return super.getPasteFeature(context);
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDirectEditingFeature getDirectEditingFeature(IDirectEditingContext context) {
      if (!isReadOnly()) {
         return super.getDirectEditingFeature(context);
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IFeature[] getDragAndDropFeatures(IPictogramElementContext context) {
      if (!isReadOnly()) {
         return super.getDragAndDropFeatures(context);
      }
      else {
         return new IFeature[0];
      }
   }

   /**
    * Checks if the diagram is read-only or editable.
    * @return {@code true} read-only, {@code false} editable.
    */
   public boolean isReadOnly() {
      return readOnly;
   }

   /**
    * Defines if the diagram is read-only or editable.
    * @param readOnly {@code true} read-only, {@code false} editable.
    */
   public void setReadOnly(boolean readOnly) {
      this.readOnly = readOnly;
   }
}