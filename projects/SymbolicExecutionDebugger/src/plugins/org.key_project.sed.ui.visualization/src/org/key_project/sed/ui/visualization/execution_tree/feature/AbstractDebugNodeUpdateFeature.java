package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.IReason;
import org.eclipse.graphiti.features.IUpdateFeature;
import org.eclipse.graphiti.features.context.IUpdateContext;
import org.eclipse.graphiti.features.context.impl.AddContext;
import org.eclipse.graphiti.features.context.impl.AreaContext;
import org.eclipse.graphiti.features.context.impl.LayoutContext;
import org.eclipse.graphiti.features.impl.AbstractUpdateFeature;
import org.eclipse.graphiti.features.impl.Reason;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.algorithms.Text;
import org.eclipse.graphiti.mm.pictograms.ContainerShape;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.mm.pictograms.Shape;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.java.ObjectUtil;

/**
 * Provides a basic implementation of {@link IUpdateFeature} for {@link ISEDDebugNode}s.
 * @author Martin Hentschel
 */
// TODO: Implement algorithm to layout a beautiful tree
public abstract class AbstractDebugNodeUpdateFeature extends AbstractUpdateFeature {
   /**
    * The offset between the parent graphical representation and new added graphical representations.
    */
   public static final int OFFSET_TO_PARENT = 20;
   
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IUpdateFeature}.
    */   
   public AbstractDebugNodeUpdateFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canUpdate(IUpdateContext context) {
      Object bo = getBusinessObjectForPictogramElement(context.getPictogramElement());
      return canUpdateBusinessObject(bo);
   }
   
   /**
    * Checks if the give business object can be handled by this {@link IUpdateFeature}.
    * @param businessObject The business object to check.
    * @return {@code true} can update, {@code false} can not update.
    */
   protected abstract boolean canUpdateBusinessObject(Object businessObject);

   /**
    * {@inheritDoc}
    */
   @Override
   public IReason updateNeeded(IUpdateContext context) {
      try {
         PictogramElement pictogramElement = context.getPictogramElement();
         if (isNameUpdateNeeded(pictogramElement)) {
            return Reason.createTrueReason("Name is out of date.");
         }
         else {
            if (isChildrenUpdateNeeded(pictogramElement)) {
               return Reason.createTrueReason("New children available.");
            }
            else {
               return Reason.createFalseReason();
            }
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         return Reason.createFalseReason(e.getMessage());
      }
   }
   
   /**
    * Checks if the shown name in the given {@link PictogramElement}
    * is equal to the name defined by his business object 
    * ({@link ISEDDebugNode#getName()}).
    * @param pictogramElement The {@link PictogramElement} to check.
    * @return {@code true} name is different and an update is required, {@code false} name is the same and no update is required.
    * @throws DebugException Occurred Exception.
    */
   protected boolean isNameUpdateNeeded(PictogramElement pictogramElement) throws DebugException {
      String pictogramName = getPictogramName(pictogramElement);
      String businessName = getBusinessName(pictogramElement);
      return !ObjectUtil.equals(businessName, pictogramName);  
   }
   
   /**
    * Checks if all child {@link ISEDDebugNode} of the {@link ISEDDebugNode}
    * which is the business object of the given {@link PictogramElement} have
    * a graphical representation. 
    * @param pictogramElement The {@link PictogramElement} to check.
    * @return {@code false} all children have graphical representation, {@code true} at least one child has no graphical representation.
    * @throws DebugException Occurred Exception
    */
   protected boolean isChildrenUpdateNeeded(PictogramElement pictogramElement) throws DebugException {
      return !haveAllBusinessObjectChildrenHaveGraphicalRepresentation(pictogramElement);
   }
   
   /**
    * Checks if all child {@link ISEDDebugNode} of the {@link ISEDDebugNode}
    * which is the business object of the given {@link PictogramElement} have
    * a graphical representation. 
    * @param pictogramElement The {@link PictogramElement} to check.
    * @return {@code true} all children have graphical representation, {@code false} at least one child has no graphical representation.
    * @throws DebugException Occurred Exception
    */
   protected boolean haveAllBusinessObjectChildrenHaveGraphicalRepresentation(PictogramElement pictogramElement) throws DebugException {
      Object bo = getBusinessObjectForPictogramElement(pictogramElement);
      boolean childrenHavePictogramElement = true;
      if (bo instanceof ISEDDebugNode) {
         ISEDDebugNode[] children = ((ISEDDebugNode)bo).getChildren();
         int i = 0;
         while (childrenHavePictogramElement && i < children.length) {
            PictogramElement childPE = getPictogramElementForBusinessObject(children[i]);
            childrenHavePictogramElement = childPE != null;
            i++;
         }
      }
      return childrenHavePictogramElement;
   }

   /**
    * This method is similar to the method {@link IFeatureProvider#getAllPictogramElementsForBusinessObject(Object)}, 
    * but only return the first PictogramElement.
    * @param businessObject the business object
    * @return linked pictogram element.
    */
   protected PictogramElement getPictogramElementForBusinessObject(Object businessObject) {
      return getFeatureProvider().getPictogramElementForBusinessObject(businessObject);
   }
   
   /**
    * Returns the name defined in the {@link PictogramElement}.
    * @param pictogramElement The {@link PictogramElement} for that the shown name is needed.
    * @return The name in the {@link PictogramElement}.
    */
   protected String getPictogramName(PictogramElement pictogramElement) {
      Text text = findNameText(pictogramElement);
      if (text != null) {
         return text.getValue();
      }
      else {
         return null;
      }
   }
   
   /**
    * Returns the name defined by the business object of the given {@link PictogramElement}
    * which is {@link ISEDDebugNode#getName()}.
    * @param pictogramElement The {@link PictogramElement} for that the business name is needed.
    * @return The name defined by the business object of the given {@link PictogramElement}.
    * @throws DebugException The business name.
    */
   protected String getBusinessName(PictogramElement pictogramElement) throws DebugException {
      Object bo = getBusinessObjectForPictogramElement(pictogramElement);
      if (bo instanceof ISEDDebugNode) {
         return ((ISEDDebugNode)bo).getName();
      }
      else {
         return null;
      }
   }
   
   /**
    * Finds the {@link Text} which shows the name ({@link ISEDDebugNode#getName()}).
    * @param pictogramElement The {@link PictogramElement} to search the {@link Text} in.
    * @return The found {@link Text} or {@code null} if no one was found.
    */
   protected Text findNameText(PictogramElement pictogramElement) {
      Text result = null;
      if (pictogramElement.getGraphicsAlgorithm() instanceof Text) {
         result = (Text)pictogramElement.getGraphicsAlgorithm();
      }
      else if (pictogramElement instanceof ContainerShape) {
         ContainerShape cs = (ContainerShape)pictogramElement;
         for (Shape shape : cs.getChildren()) {
            result = findNameText(shape);
         }
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean update(IUpdateContext context) {
      try {
         // Define monitor to use
         IProgressMonitor monitor;
         Object contextMonitor = context.getProperty(ExecutionTreeUtil.CONTEXT_PROPERTY_MONITOR);
         if (contextMonitor instanceof IProgressMonitor) {
            monitor = (IProgressMonitor)contextMonitor;
         }
         else {
            monitor = new NullProgressMonitor();
         }
         // Retrieve name from business model
         PictogramElement pictogramElement = context.getPictogramElement();
         monitor.beginTask("Update element: " + pictogramElement, 2);
         boolean success = updateName(pictogramElement, new SubProgressMonitor(monitor, 1));
         monitor.worked(1);
         if (success) {
            success = updateChildren(pictogramElement, new SubProgressMonitor(monitor, 1));
         }
         monitor.worked(2);
         monitor.done();
         return success;
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         return false;
      }
   }

   /**
    * Updates the shown name in the given {@link PictogramElement}.
    * @param pictogramElement The {@link PictogramElement} to update.
    * @param monitor The {@link IProgressMonitor} to use.
    * @return {@code true}, if update process was successful
    * @throws DebugException Occurred Exception.
    */
   protected boolean updateName(PictogramElement pictogramElement, 
                                IProgressMonitor monitor) throws DebugException {
      try {
         if (!monitor.isCanceled()) {
            // Set name in pictogram model
            monitor.beginTask("Update labels", 1);
            Text text = findNameText(pictogramElement);
            if (text != null) {
               // Change value
               String businessName = getBusinessName(pictogramElement);
               text.setValue(businessName);
               // Optimize layout
               LayoutContext layoutContext = new LayoutContext(pictogramElement);
               layoutContext.putProperty(AbstractDebugNodeLayoutFeature.WIDTH_TO_SET, AbstractDebugNodeAddFeature.computeInitialWidth(getDiagram(), businessName, text.getFont()));
               layoutContext.putProperty(AbstractDebugNodeLayoutFeature.HEIGHT_TO_SET, AbstractDebugNodeAddFeature.computeInitialHeight(getDiagram(), businessName, text.getFont()));
               getFeatureProvider().layoutIfPossible(layoutContext);
               // Add children
               return true;
            }
            else {
               return false;
            }
         }
         else {
            return false;
         }
      }
      finally {
         monitor.worked(1);
         monitor.done();
      }
   }
   
   /**
    * Updates the children of the {@link ISEDDebugNode} represented
    * by the given {@link PictogramElement}.
    * @param pictogramElement The {@link PictogramElement} to update.
    * @param monitor The {@link IProgressMonitor} to use.
    * @return {@code true}, if update process was successful
    * @throws DebugException Occurred Exception.
    */
   protected boolean updateChildren(PictogramElement pictogramElement, 
                                    IProgressMonitor monitor) throws DebugException {
      monitor.beginTask("Update children", IProgressMonitor.UNKNOWN);
      try {
         if (!monitor.isCanceled()) {
            Object bo = getBusinessObjectForPictogramElement(pictogramElement);
            if (bo instanceof ISEDDebugNode) {
               ISEDDebugNode[] children = ((ISEDDebugNode)bo).getChildren();
               for (ISEDDebugNode child : children) {
                  if (!monitor.isCanceled()) {
                     PictogramElement childPE = getPictogramElementForBusinessObject(child);
                     if (childPE == null) {
                        createGraphicalRepresentationForSubtree(pictogramElement, child, monitor);
                     }
                  }
               }
            }
         }
         return true;
      }
      finally {
         monitor.done();
      }
   }
   
   /**
    * Creates a new graphical representation for the given {@link ISEDDebugNode}
    * and all of his children.
    * @param parent The {@link PictogramElement} of {@link ISEDDebugNode#getParent()}.
    * @param root The {@link ISEDDebugNode} for that a graphical representation is needed.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void createGraphicalRepresentationForSubtree(PictogramElement parent, 
                                                          ISEDDebugNode root,
                                                          IProgressMonitor monitor) throws DebugException {
      if (!monitor.isCanceled()) {
         // Add root ISEDDebugNode
         AreaContext areaContext = new AreaContext();
         if (parent != null) {
            GraphicsAlgorithm parentGA = parent.getGraphicsAlgorithm();
            areaContext.setX(parentGA.getX()); 
            areaContext.setY(parentGA.getY() + parentGA.getHeight() + OFFSET_TO_PARENT);
         }
         else {
            areaContext.setLocation(0, 0);
         }
         AddContext addContext = new AddContext(areaContext, root);
         addContext.setTargetContainer(getDiagram());
         parent = getFeatureProvider().addIfPossible(addContext);
         // Add subtree of the given root ISEDDebugNode
         ISEDDebugNode[] children = root.getChildren();
         for (ISEDDebugNode child : children) {
            createGraphicalRepresentationForSubtree(parent, child, monitor);
         }
      }
      monitor.worked(1);
   }
}
