package org.key_project.sed.ui.visualization.object_diagram.feature;

import org.eclipse.graphiti.datatypes.IDimension;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.IAddContext;
import org.eclipse.graphiti.features.impl.AbstractAddShapeFeature;
import org.eclipse.graphiti.mm.algorithms.Polyline;
import org.eclipse.graphiti.mm.algorithms.RoundedRectangle;
import org.eclipse.graphiti.mm.algorithms.Text;
import org.eclipse.graphiti.mm.algorithms.styles.Orientation;
import org.eclipse.graphiti.mm.pictograms.ContainerShape;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.mm.pictograms.Shape;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.eclipse.graphiti.services.IPeCreateService;
import org.key_project.sed.ui.visualization.model.od.ODObject;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramStyleUtil;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;

/**
 * Implementation of {@link IAddFeature} for {@link ODObject}s.
 * @author Martin Hentschel
 */
public class ObjectAddFeature extends AbstractAddShapeFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public ObjectAddFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canAdd(IAddContext context) {
      // check if user wants to add a EClass
      if (context.getNewObject() instanceof ODObject) {
         // check if user wants to add to a diagram
         if (context.getTargetContainer() instanceof Diagram) {
            return true;
         }
      }
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public PictogramElement add(IAddContext context) {
      ODObject addedObject = (ODObject)context.getNewObject();
      ContainerShape targetContainer = context.getTargetContainer();

      // CONTAINER SHAPE WITH ROUNDED RECTANGLE
      IPeCreateService peCreateService = Graphiti.getPeCreateService();
      ContainerShape containerShape = peCreateService.createContainerShape(targetContainer, true);

      // check whether the context has a size (e.g. from a create feature)
      // otherwise define a default size for the shape
      final int width = context.getWidth() < ObjectLayoutFeature.MIN_WIDTH ? ObjectLayoutFeature.MIN_WIDTH : context.getWidth();
      final int height = context.getHeight() < ObjectLayoutFeature.MIN_HEIGHT ? ObjectLayoutFeature.MIN_HEIGHT : context.getHeight();
      IGaService gaService = Graphiti.getGaService();

      // if added object has no resource add it to diagram.
      if (addedObject.eResource() == null) {
         ObjectDiagramUtil.getModel(getDiagram()).getObjects().add(addedObject);
      }

      // create and set graphics algorithm
      RoundedRectangle roundedRectangle = gaService.createRoundedRectangle(containerShape, 20, 20);
      roundedRectangle.setStyle(ObjectDiagramStyleUtil.getStyleForObject(getDiagram()));
      gaService.setLocationAndSize(roundedRectangle, context.getX(), context.getY(), width, height);
      // create link and wire it
      link(containerShape, addedObject);

      // create shape for text
      Shape textShape = peCreateService.createShape(containerShape, false);
      // create and set text graphics algorithm
      Text text = gaService.createText(textShape, addedObject.getName() + " : " + addedObject.getType());
      text.setStyle(ObjectDiagramStyleUtil.getStyleForObjectText(getDiagram()));
      text.setHorizontalAlignment(Orientation.ALIGNMENT_CENTER);
      // Compute text height
      IDimension textDimension = GraphitiUtil.calculateStringSize(text.getValue(), gaService.getFont(text, true));
      final int textHeight = textDimension != null ? textDimension.getHeight() : 20;
      // vertical alignment has as default value "center"
      gaService.setLocationAndSize(text, 0, ObjectDiagramUtil.VERTICAL_OFFSET, width, textHeight);
      // create link and wire it
      link(textShape, addedObject);

      // create shape for line
      Shape polylineShape = peCreateService.createShape(containerShape, false);
      // create and set graphics algorithm
      Polyline polyline = gaService.createPolyline(polylineShape, new int[] { 0, 0, width, 0 });
      polyline.setStyle(ObjectDiagramStyleUtil.getStyleForObject(getDiagram()));
      gaService.setLocationAndSize(polyline, 0, textHeight + (2 * ObjectDiagramUtil.VERTICAL_OFFSET), width, polyline.getLineWidth());
      
      // add a chopbox anchor to the shape 
      peCreateService.createChopboxAnchor(containerShape);

      // call the layout feature
      layoutPictogramElement(containerShape);

      return containerShape;
   }
}