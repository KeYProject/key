package org.key_project.sed.ui.visualization.object_diagram.provider;

import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.ICreateConnectionFeature;
import org.eclipse.graphiti.features.ICreateFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.ILayoutFeature;
import org.eclipse.graphiti.features.IMoveShapeFeature;
import org.eclipse.graphiti.features.IReconnectionFeature;
import org.eclipse.graphiti.features.IResizeShapeFeature;
import org.eclipse.graphiti.features.context.IAddContext;
import org.eclipse.graphiti.features.context.ILayoutContext;
import org.eclipse.graphiti.features.context.IMoveShapeContext;
import org.eclipse.graphiti.features.context.IReconnectionContext;
import org.eclipse.graphiti.features.context.IResizeShapeContext;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.ui.features.DefaultFeatureProvider;
import org.key_project.sed.ui.visualization.model.od.ODAssociation;
import org.key_project.sed.ui.visualization.model.od.ODObject;
import org.key_project.sed.ui.visualization.model.od.ODState;
import org.key_project.sed.ui.visualization.model.od.ODValue;
import org.key_project.sed.ui.visualization.object_diagram.feature.AssociationAddFeature;
import org.key_project.sed.ui.visualization.object_diagram.feature.AssociationCreateFeature;
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
      return new ICreateFeature[] { new StateCreateFeature(this),
                                    new ObjectCreateFeature(this),
                                    new ValueCreateFeature(this) };
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
      return new ICreateConnectionFeature[] { new AssociationCreateFeature(this) };
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IReconnectionFeature getReconnectionFeature(IReconnectionContext context) {
       return new AssociationReconnectionFeature(this);
   }
}
