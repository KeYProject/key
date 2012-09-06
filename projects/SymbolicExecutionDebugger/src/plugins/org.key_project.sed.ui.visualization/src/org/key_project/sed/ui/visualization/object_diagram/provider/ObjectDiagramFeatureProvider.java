package org.key_project.sed.ui.visualization.object_diagram.provider;

import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.ICreateConnectionFeature;
import org.eclipse.graphiti.features.ICreateFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.ILayoutFeature;
import org.eclipse.graphiti.features.IReconnectionFeature;
import org.eclipse.graphiti.features.context.IAddContext;
import org.eclipse.graphiti.features.context.ILayoutContext;
import org.eclipse.graphiti.features.context.IReconnectionContext;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.ui.features.DefaultFeatureProvider;
import org.key_project.sed.ui.visualization.model.od.ODAssociation;
import org.key_project.sed.ui.visualization.model.od.ODObject;
import org.key_project.sed.ui.visualization.object_diagram.feature.AssociationAddFeature;
import org.key_project.sed.ui.visualization.object_diagram.feature.AssociationCreateFeature;
import org.key_project.sed.ui.visualization.object_diagram.feature.AssociationReconnectionFeature;
import org.key_project.sed.ui.visualization.object_diagram.feature.ObjectAddFeature;
import org.key_project.sed.ui.visualization.object_diagram.feature.ObjectCreateFeature;
import org.key_project.sed.ui.visualization.object_diagram.feature.ObjectLayoutFeature;

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
   public IAddFeature getAddFeature(IAddContext context) {
      if (context.getNewObject() instanceof ODObject) {
         return new ObjectAddFeature(this);
      }
      else if (context.getNewObject() instanceof ODAssociation) {
         return new AssociationAddFeature(this);
      }
      else {
         return super.getAddFeature(context);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ICreateFeature[] getCreateFeatures() {
      return new ICreateFeature[] { new ObjectCreateFeature(this) };
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
      else {
         return super.getLayoutFeature(context);
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
