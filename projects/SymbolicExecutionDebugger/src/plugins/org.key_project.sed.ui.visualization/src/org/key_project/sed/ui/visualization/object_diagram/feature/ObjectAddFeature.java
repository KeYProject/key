package org.key_project.sed.ui.visualization.object_diagram.feature;

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
      Diagram targetDiagram = (Diagram) context.getTargetContainer();

      // CONTAINER SHAPE WITH ROUNDED RECTANGLE
      IPeCreateService peCreateService = Graphiti.getPeCreateService();
      ContainerShape containerShape = peCreateService.createContainerShape(targetDiagram, true);

      // check whether the context has a size (e.g. from a create feature)
      // otherwise define a default size for the shape
      final int width = context.getWidth() <= 0 ? 100 : context.getWidth();
      final int height = context.getHeight() <= 0 ? 50 : context.getHeight();
      IGaService gaService = Graphiti.getGaService();
      RoundedRectangle roundedRectangle; // need to access it later

      {
         // create and set graphics algorithm
         roundedRectangle = gaService.createRoundedRectangle(containerShape, 5, 5);
         roundedRectangle.setStyle(ObjectDiagramStyleUtil.getStyleForObject(getDiagram()));
         gaService.setLocationAndSize(roundedRectangle, context.getX(), context.getY(), width, height);

         // if added object has no resource add it to diagram.
         if (addedObject.eResource() == null) {
            ObjectDiagramUtil.getModel(getDiagram()).getObjects().add(addedObject);
         }
         // create link and wire it
         link(containerShape, addedObject);
      }

      // SHAPE WITH LINE
      {
         // create shape for line
         Shape shape = peCreateService.createShape(containerShape, false);

         // create and set graphics algorithm
         Polyline polyline = gaService.createPolyline(shape, new int[] { 0, 20, width, 20 });
         polyline.setStyle(ObjectDiagramStyleUtil.getStyleForObject(getDiagram()));
      }

      // SHAPE WITH TEXT
      {
         // create shape for text
         Shape shape = peCreateService.createShape(containerShape, false);

         // create and set text graphics algorithm
         Text text = gaService.createText(shape, addedObject.getName() + " : " + addedObject.getType());
         text.setStyle(ObjectDiagramStyleUtil.getStyleForObjectText(getDiagram()));
         text.setHorizontalAlignment(Orientation.ALIGNMENT_CENTER);
         // vertical alignment has as default value "center"
         gaService.setLocationAndSize(text, 0, 0, width, 20);

         // create link and wire it
         link(shape, addedObject);
      }
      
      // add a chopbox anchor to the shape 
      peCreateService.createChopboxAnchor(containerShape);

      // call the layout feature
      layoutPictogramElement(containerShape);

      return containerShape;
   }
}