package org.key_project.sed.ui.visualization.object_diagram.feature;

import org.eclipse.graphiti.features.ICreateFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICreateContext;
import org.eclipse.graphiti.features.impl.AbstractCreateFeature;
import org.eclipse.graphiti.mm.pictograms.ContainerShape;
import org.key_project.sed.ui.visualization.model.od.ODObject;
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
      ContainerShape shape = context.getTargetContainer();
      if (shape != null) {
         Object bo = getBusinessObjectForPictogramElement(shape);
         return bo instanceof ODObject;
      }
      else {
         return false;
      }
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
         ODObject bo = (ODObject)getBusinessObjectForPictogramElement(context.getTargetContainer());
         bo.getValues().add(value);
         // Do the add
         addGraphicalRepresentation(context, value);
         // Return newly created business object(s)
         return new Object[] { value };
      }
   }
}