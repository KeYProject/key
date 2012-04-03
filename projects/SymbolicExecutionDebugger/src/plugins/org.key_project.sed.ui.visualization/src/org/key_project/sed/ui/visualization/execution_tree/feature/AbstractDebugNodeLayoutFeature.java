package org.key_project.sed.ui.visualization.execution_tree.feature;

import java.util.List;

import org.eclipse.graphiti.datatypes.IDimension;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.ILayoutFeature;
import org.eclipse.graphiti.features.context.ILayoutContext;
import org.eclipse.graphiti.features.impl.AbstractLayoutFeature;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.pictograms.ContainerShape;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.mm.pictograms.Shape;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.key_project.sed.core.model.ISEDDebugNode;

/**
 * Provides a basic implementation of {@link ILayoutFeature} for {@link ISEDDebugNode}s.
 * @author Martin Hentschel
 */
public abstract class AbstractDebugNodeLayoutFeature extends AbstractLayoutFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link ILayoutFeature}.
    */
   public AbstractDebugNodeLayoutFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canLayout(ILayoutContext context) {
      PictogramElement pe = context.getPictogramElement();
      boolean canLayout = false;
      if (pe instanceof ContainerShape) {
         Object[] bos = getAllBusinessObjectsForPictogramElement(pe);
         canLayout = bos.length == 1 && canLayoutBusinessObject(bos[0]);
      }
      return canLayout;
   }
   
   /**
    * Checks if this {@link ILayoutFeature} can layout the given business object.
    * @param businessObject The business object to check.
    * @return {@code true} layout business object, {@code false} = do not layout business object.
    */
   protected abstract boolean canLayoutBusinessObject(Object businessObject);

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean layout(ILayoutContext context) {
      boolean anythingChanged = false;
      ContainerShape containerShape = (ContainerShape) context.getPictogramElement();
      GraphicsAlgorithm containerGa = containerShape.getGraphicsAlgorithm();

      // Compute minimal width and height
      final int MIN_WIDTH = AbstractDebugNodeAddFeature.computeMinWidth(getDiagram());
      final int MIN_HEIGHT = AbstractDebugNodeAddFeature.computeMinHeight(getDiagram());
      
      // height
      if (containerGa.getHeight() < MIN_HEIGHT) {
         containerGa.setHeight(MIN_HEIGHT);
         anythingChanged = true;
      }

      // width
      if (containerGa.getWidth() < MIN_WIDTH) {
         containerGa.setWidth(MIN_WIDTH);
         anythingChanged = true;
      }

      int containerWidth = containerGa.getWidth();
      int containerHeight = containerGa.getHeight();
     
      
      List<Shape> shapes = containerShape.getChildren();
      if (layoutImageShape(shapes.get(0), containerWidth, containerHeight)) {
         anythingChanged = true;
      }
      if (layoutTextShape(shapes.get(1), containerWidth, containerHeight)) {
         anythingChanged = true;
      }
      return anythingChanged;
   }
   
   /**
    * Layouts the {@link Shape} which contains the image.
    * @param shape The {@link Shape} to layout.
    * @param containerWidth The width to use.
    * @param containerHeight The height to use.
    * @return {@code true} something has changed, {@code false} nothing has changed.
    */
   protected boolean layoutTextShape(Shape shape, int containerWidth, int containerHeight) {
      GraphicsAlgorithm graphicsAlgorithm = shape.getGraphicsAlgorithm();
      IGaService gaService = Graphiti.getGaService();
      IDimension size = gaService.calculateSize(graphicsAlgorithm);
      if (containerWidth != size.getWidth()) {
         gaService.setWidth(graphicsAlgorithm, containerWidth - (StatementAddFeature.MARGIN + StatementAddFeature.IMAGE_WIDTH + StatementAddFeature.MARGIN + StatementAddFeature.MARGIN));
         gaService.setHeight(graphicsAlgorithm, containerHeight);
         return true;
      }
      else {
         return false;
      }
   }
   
   /**
    * Layouts the {@link Shape} which contains the text.
    * @param shape The {@link Shape} to layout.
    * @param containerWidth The width to use.
    * @param containerHeight The height to use.
    * @return {@code true} something has changed, {@code false} nothing has changed.
    */
   protected boolean layoutImageShape(Shape shape, int containerWidth, int containerHeight) {
      GraphicsAlgorithm graphicsAlgorithm = shape.getGraphicsAlgorithm();
      IGaService gaService = Graphiti.getGaService();
      IDimension size = gaService.calculateSize(graphicsAlgorithm);
      if (containerWidth != size.getWidth()) {
         gaService.setHeight(graphicsAlgorithm, containerHeight);
         return true;
      }
      else {
         return false;
      }
   }
}