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

package org.key_project.sed.ui.visualization.execution_tree.feature;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.IReason;
import org.eclipse.graphiti.features.IUpdateFeature;
import org.eclipse.graphiti.features.context.IUpdateContext;
import org.eclipse.graphiti.features.context.impl.AddContext;
import org.eclipse.graphiti.features.context.impl.AreaContext;
import org.eclipse.graphiti.features.context.impl.LayoutContext;
import org.eclipse.graphiti.features.context.impl.UpdateContext;
import org.eclipse.graphiti.features.impl.AbstractUpdateFeature;
import org.eclipse.graphiti.features.impl.Reason;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.algorithms.RoundedRectangle;
import org.eclipse.graphiti.mm.algorithms.Text;
import org.eclipse.graphiti.mm.pictograms.ContainerShape;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.mm.pictograms.Shape;

import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.model.ISEDBaseMethodReturn;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDExceptionalTermination;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.core.util.ISEDIterator;
import org.key_project.sed.core.util.NodeUtil;
import org.key_project.sed.core.util.SEDMethodPreorderIterator;
import org.key_project.sed.core.util.SEDPreorderIterator;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeStyleUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilterWithException;
import org.key_project.util.java.StringUtil;

/**
 * <p>
 * Provides a basic implementation of {@link IUpdateFeature} for {@link ISEDDebugNode}s.
 * </p>
 * </p>
 * A subtree is constructed as follows during execution of {@link #update(IUpdateContext)}
 * 
 * <ol>
 *    <li>Update label of current node via {@link #updateName(PictogramElement, IProgressMonitor)} </li>
 *    <li>
 *       Update sub tree via {@link #updateChildren(PictogramElement, IProgressMonitor)}
 *       <ol>
 *          <li>
 *             Add missing graphical representations in a tree where each branch is left centered.
 *             Result is a list of leaf nodes computed via {@link #updateChildrenLeftAligned(ISEDDebugElement, IProgressMonitor, int)}
 *             <ol>
 *                <li>Iterate over subtree in order.</li>
 *                <li>First branch (ends in first leaf node) is completely left centered with x = 0.</li>
 *                <li>
 *                   If a further branch is detected, the maximal width of the previous 
 *                   branch is computed via {@link #computeSubTreeBounds(ISEDDebugNode)}
 *                   and the x coordinate is the maximal bound (x + width) + a given offset of two grid units.
 *                </li>
 *             </ol>
 *          </li>
 *          <li>
 *             Center whole sub tree starting from its branches leaf nodes via {@link #centerChildren(Set, IProgressMonitor)}.
 *             <ol>
 *                <li>Iterate over all given leaf nodes. (Start with the found one via {@link #updateChildrenLeftAligned(ISEDDebugElement, IProgressMonitor, int)} and continue with nodes which children are completly centered)</li>
 *                <li>
 *                   If leaf node has children (added during step 4) compute x offset to center branch under his children.
 *                </li>
 *                <li>
 *                   Go back to parents until root is reached (parent is {@code null} or multiple children are detected.
 *                   During backward iteration collect maximal width of the elements.
 *                </li>
 *                <li>
 *                   If the iteration stopped because the parent has multiple children,
 *                   at the parent to leaf node to layout it later on same way. 
 *                </li>
 *                <li>
 *                   Go back to starting child (leaf node) and center each element with the computed maximal width.
 *                </li>
 *                <li>
 *                   If parents maximal width is greater than the maximal width of the children move the children again to the right to center them.
 *                </li>
 *             </ol>
 *          </li>
 *          <li>
 *             Move righter branches if the width of a modified branch was expanded via {@link #updateParents(PictogramElement, IProgressMonitor)}.
 *             <ol>
 *                <li>Find most left node via {@link #findMostLeftSiblingPE(ISEDDebugNode)}</li>
 *                <li>Compute distance to move as most right node of branch + offset - most left sibling</li>
 *                <li>Move all righter nodes via {@link #moveRighterNodes(ISEDDebugNode, int, IProgressMonitor)}</li>
 *             </ol>
 *          </li>
 *       </ol>
 *    </li>
 * </ol>
 * <p>
 * @author Martin Hentschel
 */
public abstract class AbstractDebugNodeUpdateFeature extends AbstractUpdateFeature {
   /**
    * Key used in {@link UpdateContext#getProperty(Object)} which specifies that the style has to be updated. 
    * The value is an instance of {@link Boolean}.
    */
   public static final String KEY_UPDATE_STYLE = "updateStyle";
   
   /**
    * Key used in {@link UpdateContext#getProperty(Object)} to specify the changed {@link ISEDDebugNode}
    * for which the style of its {@link PictogramElement} has to be updated.
    * The value is an instance of {@link ISEDDebugNode}.
    */
   public static final String KEY_SED_NODE = "sedNode";
   
   /**
    * The maximal x coordinate which is used by the previous
    * {@link ISEDDebugTarget} in {@link #updateChildren(PictogramElement, IProgressMonitor)}.
    */
   private int maxX;
   
   /**
    * The OFFSET between two nodes
    */
   protected final int OFFSET = getDiagram().getGridUnit() * 2;
   
   /**
    * The OFFSET between the Rect of a Method an the Methodnodes
    * -> MethodCallAddFeature Rectwidth + METOFF * 2
    */
   protected final int METOFF = 10;
   
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
      Object updateStyle = context.getProperty(KEY_UPDATE_STYLE);
      if (updateStyle instanceof Boolean && ((Boolean)updateStyle).booleanValue()) {
         return context.getPictogramElement() != null;
      }
      else {
         Object bo = getBusinessObjectForPictogramElement(context.getPictogramElement());
         return canUpdateBusinessObject(bo);
      }
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
      Object updateStyle = context.getProperty(KEY_UPDATE_STYLE);
      if (updateStyle instanceof Boolean && ((Boolean)updateStyle).booleanValue()) {
         return Reason.createTrueReason("Style is out of date.");
      }
      else {
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
      return !StringUtil.equalIgnoreWhiteSpace(businessName, pictogramName);
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
         ISEDDebugNode[] children = NodeUtil.getChildren((ISEDDebugNode)bo);
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
      if(businessObject instanceof ISEDMethodCall) {
         return getPictogramElementForBusinessObject(businessObject, 1);
      }
      
      return getPictogramElementForBusinessObject(businessObject, 0);
   }
   
   protected PictogramElement getPictogramElementForBusinessObject(Object businessObject, int i) {
      if(i < 0 || i > 1)
         return null;
      
      if(i == 0)
         return getFeatureProvider().getPictogramElementForBusinessObject(businessObject);

      PictogramElement[] pes = getFeatureProvider().getAllPictogramElementsForBusinessObject(businessObject);
      return pes == null || pes.length < 1 ? null : pes[1];
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
      else if (pictogramElement instanceof ContainerShape && pictogramElement.getGraphicsAlgorithm() instanceof  RoundedRectangle) {
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
      Object updateStyle = context.getProperty(KEY_UPDATE_STYLE);
      if (updateStyle instanceof Boolean && ((Boolean)updateStyle).booleanValue()) {
         Object nodeProp = context.getProperty(KEY_SED_NODE);
         ISEDDebugNode bo = nodeProp instanceof ISEDDebugNode ? (ISEDDebugNode)nodeProp : null;
         if (bo == null) {
            bo = (ISEDDebugNode)getFeatureProvider().getBusinessObjectForPictogramElement(context.getPictogramElement());
         }
         return updateStyle(context.getPictogramElement(), bo);
      }
      else {
         try {
            // Define monitor to use
            IProgressMonitor monitor = GraphitiUtil.getProgressMonitor(context);
            // Update name
            PictogramElement pictogramElement = context.getPictogramElement();
            monitor.beginTask("Update element: " + pictogramElement, 3);
            boolean success = updateName(pictogramElement, new SubProgressMonitor(monitor, 1));
            monitor.worked(1);
            
            
//            System.out.println("O2U: " + getBusinessName(pictogramElement));
            
            
            // Update children, they have the correct layout after this step
//            final int OFFSET = getDiagram().getGridUnit() * 2;
            if (success) {
               success = updateChildren(pictogramElement, OFFSET, new SubProgressMonitor(monitor, 1));
            }
            monitor.worked(1);
            // Update parents, because children maybe have now a bigger width and overlap with other branches
            if (success) {
               success = updateParents(pictogramElement, OFFSET, new SubProgressMonitor(monitor, 1));
            }
            monitor.worked(1);
            if(success) {
               Object bo = getBusinessObjectForPictogramElement(pictogramElement);
               ISEDDebugNode node = bo instanceof ISEDDebugNode ? (ISEDDebugNode)bo : null;
               
               if(node != null) {
                  adjustRects(node, monitor);
               }
            }
            monitor.done();
            return success;
         }
         catch (DebugException e) {
            LogUtil.getLogger().logError(e);
            return false;
         }
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
    * @param offsetBetweenPictogramElements The offset between {@link PictogramElement}s.
    * @param monitor The {@link IProgressMonitor} to use.
    * @return {@code true}, if update process was successful
    * @throws DebugException Occurred Exception.
    */
   protected boolean updateChildren(PictogramElement pictogramElement,
                                    int offsetBetweenPictogramElements,
                                    IProgressMonitor monitor) throws DebugException {
      monitor.beginTask("Update children", IProgressMonitor.UNKNOWN);
      maxX = 0;
      try {
         if (!monitor.isCanceled()) {
            Object[] bos = getAllBusinessObjectsForPictogramElement(pictogramElement);
            int i = 0;
            while (i < bos.length && !monitor.isCanceled()) {
               if (bos[i] instanceof ISEDDebugElement) {
                  // Add all children left aligned
                  Set<ISEDDebugNode> leafs = updateChildrenLeftAligned((ISEDDebugElement)bos[i], monitor, offsetBetweenPictogramElements, maxX);
                  maxX += offsetBetweenPictogramElements;
                  monitor.worked(1);
                  // Center sub tree
                  ISEDDebugNode start = bos[i] instanceof ISEDDebugNode ? (ISEDDebugNode) bos[i] : null;
                  centerChildren(start, new HashSet<ISEDDebugNode>(leafs), monitor);
                  if(bos[i] instanceof ISEDDebugNode) {
                     adjustRects((ISEDDebugNode) bos[i], monitor);
                     updateParents(getPictogramElementForBusinessObject(start), OFFSET, new SubProgressMonitor(monitor, 1));
                  }
                  monitor.worked(1);
               }
               i++;
            }
         }
         return true;
      }
      finally {
         monitor.done();
      }
   }

   /**
    * Creates for each element starting at the given business object
    * a graphical representation and forms a left aligned tree.
    * @param businessObject The business object to create graphical representations for.
    * @param monitor The {@link IProgressMonitor} to use.
    * @param offsetBetweenPictogramElements The offset between {@link PictogramElement}s.
    * @param initialX The initial X value which is used if no parentPE is defined.
    * @return The found leaf {@link ISEDDebugNode}s.
    * @throws DebugException Occurred Exception.
    */
   protected Set<ISEDDebugNode> updateChildrenLeftAligned(ISEDDebugElement businessObject, 
                                                          IProgressMonitor monitor, 
                                                          int offsetBetweenPictogramElements,
                                                          int initialX) throws DebugException {
      Set<ISEDDebugNode> leafs = new LinkedHashSet<ISEDDebugNode>();
      ISEDIterator iter = new SEDPreorderIterator(businessObject);
      
      if(businessObject instanceof ISEDMethodCall)
      {
         ISEDMethodCall mc = (ISEDMethodCall) businessObject;
         if(!mc.isCollapsed()){
            iter = new SEDMethodPreorderIterator(mc);
         }
      }

//      while (iter.hasNext() && !monitor.isCanceled()) {
      while (iter.hasNext() && !monitor.isCanceled()) {
         ISEDDebugElement next = iter.next();
         
         // Ignore the bo, because either it is ISEDDebugTarget (the very first bo) which has no graphical representation
         // or its a parentnode which already has a graphical representation
         if(next == businessObject) {
            continue;
         }

         ISEDDebugNode nextNode = (ISEDDebugNode)next;
//         System.out.println("NextNode: " + nextNode);
         PictogramElement nextPE = getPictogramElementForBusinessObject(next);
         if (nextPE == null) {
            createGraphicalRepresentationForNode(nextNode, offsetBetweenPictogramElements, initialX);
            nextPE = getPictogramElementForBusinessObject(nextNode);
            if (nextPE != null) {
               // Update maxX to make sure that ISEDDebugTargets don't overlap each other.
               GraphicsAlgorithm nextGA = nextPE.getGraphicsAlgorithm();
               
               if(nextNode instanceof ISEDMethodCall) {
                  GraphicsAlgorithm rectGA = getPictogramElementForBusinessObject(nextNode, 0).getGraphicsAlgorithm();
                  rectGA.setWidth(rectGA.getWidth() + 2 * METOFF);
               }

               if(nextGA.getX() + nextGA.getWidth() > maxX)
                  maxX = nextGA.getX() + nextGA.getWidth();
               
               ISEDMethodCall node = null;
               
               if(!ArrayUtil.isEmpty(nextNode.getCallStack())) {
                  node = (ISEDMethodCall) nextNode.getCallStack()[0];
               }
               else if(NodeUtil.getParent(nextNode) instanceof ISEDMethodCall) {
                  node = (ISEDMethodCall) NodeUtil.getParent(nextNode);
               }

               if(node != null) {
                  updateAllMethodRectHeights(node, nextGA, nextNode instanceof ISEDBaseMethodReturn);
               }
            }
            if (ArrayUtil.isEmpty(NodeUtil.getChildren(nextNode))) {
               leafs.add(nextNode);
            }
         }
         else if((nextNode instanceof ISEDBaseMethodReturn) && !leafs.contains(nextNode)){
            GraphicsAlgorithm parentGA = getPictogramElementForBusinessObject(NodeUtil.getParent(nextNode)).getGraphicsAlgorithm();
            GraphicsAlgorithm nextGA = nextPE.getGraphicsAlgorithm();
            nextGA.setX(parentGA.getX());
            
            if(nextGA.getY() < parentGA.getY() + parentGA.getHeight() + OFFSET) {
               moveSubTreeVertical(nextNode, parentGA.getY() + parentGA.getHeight() + OFFSET - nextGA.getY());
               updateAllMethodRectHeights((ISEDMethodCall) nextNode.getCallStack()[0], nextGA, nextNode instanceof ISEDBaseMethodReturn);
            }

            leafs.add(nextNode);
         }
            
         monitor.worked(1);
      }
      return leafs;
   }
   
   /**
    * Creates a new graphical representation for the given {@link ISEDDebugNode}.
    * @param node The {@link ISEDDebugNode} for that a graphical representation is needed.
    * @param offsetBetweenPictogramElements The offset between {@link PictogramElement}s, e.g. to parent or to previous sibling.
    * @param initialX The initial X value which is used if no parentPE is defined.
    * @throws DebugException Occurred Exception.
    */
   protected void createGraphicalRepresentationForNode(ISEDDebugNode node,
                                                       int offsetBetweenPictogramElements,
                                                       int initialX) throws DebugException { 
      AreaContext areaContext = new AreaContext();
      ISEDDebugNode parent = NodeUtil.getParent(node);

      if(parent != null)
      {
         PictogramElement pe = getPictogramElementForBusinessObject(parent);
         GraphicsAlgorithm parentGA = pe.getGraphicsAlgorithm();

         int areaX = -1;
         int areaY = parentGA.getY() + parentGA.getHeight() + offsetBetweenPictogramElements;
         
         ISEDDebugNode previousSibling = ArrayUtil.getPrevious(NodeUtil.getChildren(parent, true), node);

         if (previousSibling != null) {
            int subTreeWidth = findMostRightXInSubtree(previousSibling);
            if (subTreeWidth > -1) {
               // Add right to the previous sibling directly under parent
               GraphicsAlgorithm gas = getPictogramElementForBusinessObject(previousSibling).getGraphicsAlgorithm();
               areaX = subTreeWidth + offsetBetweenPictogramElements;
               areaY = gas.getY();
            }
         }
         
         // If we dont have any previous sibling or we dont have a subtree at the previous sibling
         if(areaX == -1) {
            areaX = findMostLeftXOfBranchAbove(parent);//findMostLeftXOfBranchInParents(parent);
         }

         areaContext.setX(areaX);
         areaContext.setY(areaY);
      }
      else {
         areaContext.setLocation(initialX, getDiagram().getGridUnit());
      }

      AddContext addContext = new AddContext(areaContext, node);
      addContext.setTargetContainer(getDiagram());
      // Execute add feature manually because getFeatureProvider().addIfPossible(addContext) changes the selection
      IAddFeature feature = getFeatureProvider().getAddFeature(addContext);
      if (feature != null && feature.canExecute(addContext)) {
         feature.execute(addContext);
      }
   }
   
   /**
    * TODO
    * Computes the bounds of the sub tree starting at the given {@link ISEDDebugNode}.
    * @param root The sub tree.
    * @return The bounds of the subtree where {@link Rectangle#x()}, {@link Rectangle#y()} is the minimal point and {@link Rectangle#width()}, {@link Rectangle#height()} the maximal point. The result is {@code null} if the subtree is {@code null} or has no graphical representations.
    * @throws DebugException Occurred Exception.
    */
   protected int computeSubTreeWidth(ISEDDebugNode root) throws DebugException {
      int x = -1, width = 0;
      if (root != null) {
         ISEDIterator iter = new SEDPreorderIterator(root);
         while (iter.hasNext()) {
            ISEDDebugElement next = iter.next();
            PictogramElement nextPE = getPictogramElementForBusinessObject(next);
            System.out.println(next);
            if (nextPE != null) {
               GraphicsAlgorithm nextGA = nextPE.getGraphicsAlgorithm();
               
               if(nextGA.getX() < x || x == -1) {
                  x = nextGA.getX();
               }
               
               if(nextGA.getX() + nextGA.getWidth() > width) {
                  width = nextGA.getX() + nextGA.getWidth();
               }
            }
         }
      }
      return width - x;
   }

   /**
    * Computes the bounds of the sub tree starting at the given {@link ISEDDebugNode}.
    * @param root The sub tree.
    * @return The bounds of the subtree where {@link Rectangle#x()}, {@link Rectangle#y()} is the minimal point and {@link Rectangle#width()}, {@link Rectangle#height()} the maximal point. The result is {@code null} if the subtree is {@code null} or has no graphical representations.
    * @throws DebugException Occurred Exception.
    */
   protected Rectangle computeSubTreeBounds(ISEDDebugNode root) throws DebugException {
      Rectangle result = null;
      boolean first = true;
      if (root != null) {
         ISEDIterator iter = new SEDPreorderIterator(root);
         while (iter.hasNext()) {
            ISEDDebugElement next = iter.next();
            if(first && iter.hasNext()) {
               next = iter.next();
            }
            PictogramElement nextPE = next instanceof ISEDMethodCall ? getPictogramElementForBusinessObject(next, 0) : getPictogramElementForBusinessObject(next);
            //getPictogramElementForBusinessObject(next);
            if (nextPE != null) {
               GraphicsAlgorithm nextGA = nextPE.getGraphicsAlgorithm();
               if (result == null) {
                  result = new Rectangle(nextGA.getX(), 
                                         nextGA.getY(), 
                                         nextGA.getX() + nextGA.getWidth(), 
                                         nextGA.getY() + nextGA.getHeight());
               }
               else {
                  if (nextGA.getX() < result.x()) {
                     result.setX(nextGA.getX());
                  }
                  if (nextGA.getY() < result.y()) {
                     result.setY(nextGA.getY());
                  }
                  if (nextGA.getX() + nextGA.getWidth() > result.width()) {
                     result.setWidth(nextGA.getX() + nextGA.getWidth());
                  }
                  if (nextGA.getY() + nextGA.getHeight() > result.height()) {
                     result.setHeight(nextGA.getY() + nextGA.getHeight());
                  }
               }
            }
         }
         result.setWidth(result.width() - result.x());
      }
      return result;
   }
   
   /**
    * Centers all nodes starting from the given leaf nodes.
    * @param leafs All leaf nodes.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception
    */
   protected void centerChildren(ISEDDebugNode start, final Set<ISEDDebugNode> leafs, 
                                 IProgressMonitor monitor) throws DebugException {
      final Set<ISEDDebugNode> doneNodes = new HashSet<ISEDDebugNode>(); // Contains all already centered nodes
      while (!leafs.isEmpty() && !monitor.isCanceled()) {
         // Get leaf to center which is the first one which children are already centered (all children are contained in doneNodes) or if no centering of the child is required (not part of leafs)
         final ISEDDebugNode next = CollectionUtil.searchAndRemoveWithException(leafs, new IFilterWithException<ISEDDebugNode, DebugException>() {
            @Override
            public boolean select(ISEDDebugNode element) throws DebugException {
               boolean allChildrenDone = true;
               ISEDDebugNode[] children = NodeUtil.getChildren(element);
               int i = 0;
               while (allChildrenDone && i < children.length) {
                  if (!doneNodes.contains(children[i]) && leafs.contains(children[i])) {
                     allChildrenDone = false;
                  }
                  i++;
               }
               return allChildrenDone;
            }
         }); 
         final PictogramElement nextPE = getPictogramElementForBusinessObject(next);
         final GraphicsAlgorithm nextGA = nextPE.getGraphicsAlgorithm();
         // Compute new x margin to center current branch under his children 
         int xMargin = 0;
         int xStart = nextGA.getX();
         boolean removeChildrenRequired = false;
         boolean isMC = next instanceof ISEDMethodCall;
         
         ISEDMethodCall mc = isMC ? (ISEDMethodCall) next : null;
   
         ISEDDebugNode[] children = NodeUtil.getChildren(next, true);
         if (!ArrayUtil.isEmpty(children) && children.length > 1)
         {
            ISEDDebugNode firstChild = ArrayUtil.getFirst(children);
            ISEDDebugNode lastChild = ArrayUtil.getLast(children);
            PictogramElement firstChildPE = getPictogramElementForBusinessObject(firstChild);
            PictogramElement lastChildPE = getPictogramElementForBusinessObject(lastChild);
            int childWidth = lastChildPE.getGraphicsAlgorithm().getX() + lastChildPE.getGraphicsAlgorithm().getWidth() - 
                             firstChildPE.getGraphicsAlgorithm().getX();

            xMargin = (childWidth - nextGA.getWidth()) / 2;
            xStart = firstChildPE.getGraphicsAlgorithm().getX();
            
//            System.out.println("XM: " + xMargin + ", XS: " + xStart + ", CW: " + childWidth + ", NPEX: " + nextPE.getGraphicsAlgorithm().getX());
            
            // Make sure that the new position is not "lefter" as the old one because this area is reserved for the previous branch and they should not collapse  
            if (xMargin + xStart < nextGA.getX()) {
               
               if(!isMC || !mc.isCollapsed())
               {
                  // Collapse possible, so keep old xStart 
                  xMargin = 0;
                  xStart = nextGA.getX();
                  removeChildrenRequired = true;  
               }
               
            }
         }
         
//         System.out.println("XM: " + xMargin + ", XS: " + xStart + ", X: " + nextPE.getGraphicsAlgorithm().getX());
         
         // Go back to root or branch split and collect descendants while computing max width
         // If a parent node has more than one child it is treated as leaf node in a further iteration by adding it to leafs
         List<PictogramElement> descendantsPE = new LinkedList<PictogramElement>();
         int maxWidth = 0;
   //      boolean maxInitialised = false;
         ISEDDebugNode current = next;
         PictogramElement currentPE = nextPE;
         
         
   //      System.out.println(current);
         
         if(isMC && !mc.isCollapsed()) {
            descendantsPE.add(getPictogramElementForBusinessObject(current, 0));
   //         xStart -= METOFF;
         }
         
         boolean locked = false;
         do {
   //         System.out.println("Current: " + current);
            doneNodes.add(current); // Mark element as centered because it will be done before the next leaf node will be treated in outer most loop
            
            currentPE = getPictogramElementForBusinessObject(current); 
            descendantsPE.add(currentPE);
   
            int currentWidth = currentPE.getGraphicsAlgorithm().getWidth();
            if (currentWidth > maxWidth && (!locked || removeChildrenRequired)) {
               maxWidth = currentWidth;
               if(removeChildrenRequired)
                  xStart = currentPE.getGraphicsAlgorithm().getX();
               
               if(NodeUtil.getChildren(current).length > 1)
                  locked = true;               
            }
            
            ISEDDebugNode child = current;
            current = NodeUtil.getParent(child);
   
            if (current != null && NodeUtil.getChildren(current).length != 1) {
               // Update parent only if all of his branches are correctly centered
               if(doneNodes.containsAll(new HashSet<ISEDDebugNode>(Arrays.asList(NodeUtil.getChildren(current))))){
                  leafs.add(current);
               }
               current = null;
            }
         } while (current != null && !monitor.isCanceled());
   
         // Center collected descendants based on the computed maximal element width
         Iterator<PictogramElement> descendantIter = descendantsPE.iterator();
         while (descendantIter.hasNext() && !monitor.isCanceled()) {
            PictogramElement pe = descendantIter.next();
            GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
            int newX = xMargin + xStart + (maxWidth - ga.getWidth()) / 2; 
            ga.setX(newX);
//            ISEDDebugNode node = (ISEDDebugNode) getBusinessObjectForPictogramElement(pe);
//            System.out.println("NEWX: " + (xMargin + xStart + (maxWidth - ga.getWidth()) / 2));
//            System.out.println("N: " + node + ", ??: " + ((maxWidth - ga.getWidth()) / 2));
         }
         monitor.worked(1);

         // Center children again if required
         if (removeChildrenRequired && !ArrayUtil.isEmpty(NodeUtil.getChildren(next))) {
            ISEDDebugNode lastChild = ArrayUtil.getLast(NodeUtil.getChildren(next));
            ISEDDebugNode firstChild = ArrayUtil.getFirst(NodeUtil.getChildren(next));
            
            PictogramElement firstChildPE = getPictogramElementForBusinessObject(firstChild);
            PictogramElement lastChildPE = getPictogramElementForBusinessObject(lastChild);
            int childWidth = lastChildPE.getGraphicsAlgorithm().getX() + lastChildPE.getGraphicsAlgorithm().getWidth() - 
                             firstChildPE.getGraphicsAlgorithm().getX();

            int offset = nextGA.getX() - firstChildPE.getGraphicsAlgorithm().getX() + (nextGA.getWidth() - childWidth) / 2;
            // Center children again only if offset is positive, because otherwise an overlap with the branch next to the left is possible
            if (offset > 0) {
               SEDPreorderIterator iter = new SEDPreorderIterator(next);
               while (iter.hasNext()) {
                  ISEDDebugElement nextChild = iter.next();
                  if (nextChild != next) {
                     PictogramElement nextChildPE = getPictogramElementForBusinessObject(nextChild);
                     if (nextChildPE != null) {
                        nextChildPE.getGraphicsAlgorithm().setX(nextChildPE.getGraphicsAlgorithm().getX() + offset);
                     }
                  }
               }
            }
         }
      }
      
      if(start != null)
      {
         int mostLeftPrevious = findMostLeftXInPreviousBranch(start);
         int mostLeftFollowing = findMostLeftXInFollowingBranch(start);
         
         if(mostLeftFollowing > -1 || mostLeftPrevious > -1)
         {
            GraphicsAlgorithm nodeGA = getPictogramElementForBusinessObject(start).getGraphicsAlgorithm();
            Rectangle newChildrenSubtree = computeSubTreeBounds(start);
            int biggestWidth = findBiggestWidthInPartTreeAbove(start);
            
            if(newChildrenSubtree.width > biggestWidth)
            {
               ISEDDebugNode mostLeftNode = findMostLeftXNodeInParentBranches(start);
               GraphicsAlgorithm mlnGA = getPictogramElementForBusinessObject(mostLeftNode).getGraphicsAlgorithm();
               Rectangle subTree = computeSubTreeBounds(mostLeftNode);
               
               int diff = (newChildrenSubtree.width - biggestWidth) / 4;

               if(mostLeftFollowing > -1 && mlnGA.getX() < subTree.x && (mostLeftPrevious == -1 || mlnGA.getX() > mostLeftPrevious)) {
               
//                  if(mlnGA.getX() + mlnGA.getWidth() > mostLeftFollowing) {
                     moveONodes(start, mostLeftNode, diff, monitor);
//                  }
               }
               
               if(mostLeftPrevious > -1 && mlnGA.getX() < subTree.x && mlnGA.getX() < mostLeftPrevious) {

                  if(mlnGA.getX() + diff > subTree.x) {
                     diff = (subTree.x - mlnGA.getX()) / 2;
                  }
                  
                  if(mlnGA.getX() + mlnGA.getWidth() < nodeGA.getX() + nodeGA.getWidth()) {
                     diff /= 2;
                  }
      
                  moveLefterNodes(start, mostLeftNode, -diff, monitor);
               }
            }
         }
      }
   }
//   protected void centerChildren(ISEDDebugNode start,
//                                 final Set<ISEDDebugNode> leafs, 
//                                 IProgressMonitor monitor) throws DebugException {
//      final Set<ISEDDebugNode> doneNodes = new HashSet<ISEDDebugNode>(); // Contains all already centered nodes
//      while (!leafs.isEmpty() && !monitor.isCanceled()) {
//         // Get leaf to center which is the first one which children are already centered (all children are contained in doneNodes) or if no centering of the child is required (not part of leafs)
//         final ISEDDebugNode next = CollectionUtil.searchAndRemoveWithException(leafs, new IFilterWithException<ISEDDebugNode, DebugException>() {
//            @Override
//            public boolean select(ISEDDebugNode element) throws DebugException {
//               boolean allChildrenDone = true;
//               ISEDDebugNode[] children = NodeUtil.getChildren(element);
//               int i = 0;
//               while (allChildrenDone && i < children.length) {
//                  if (!doneNodes.contains(children[i]) && leafs.contains(children[i])) {
//                     allChildrenDone = false;
//                  }
//                  i++;
//               }
//               return allChildrenDone;
//            }
//         }); 
//         final PictogramElement nextPE = getPictogramElementForBusinessObject(next);
//         final GraphicsAlgorithm nextGA = nextPE.getGraphicsAlgorithm();
//         // Compute new x margin to center current branch under his children 
//         int xMargin = 0;
//         int xStart = nextGA.getX();
//         int xOff = 0;
//         int maxWidth = 0;
//         
//         int move = 0;
//         boolean removeChildrenRequired = false;
//         boolean isMC = next instanceof ISEDMethodCall;
//         
//         ISEDMethodCall mc = null;
//         
//         if(isMC) {
//            mc = (ISEDMethodCall) next;
//         }
//
//         ISEDDebugNode[] children = NodeUtil.getChildren(next);
//         if (!ArrayUtil.isEmpty(children) && children.length > 1)
//         {
//            ISEDDebugNode firstChild = ArrayUtil.getFirst(children);
//            ISEDDebugNode lastChild = ArrayUtil.getLast(children);
//            PictogramElement firstChildPE = getPictogramElementForBusinessObject(firstChild);
//            PictogramElement lastChildPE = getPictogramElementForBusinessObject(lastChild);
//            int childWidth = lastChildPE.getGraphicsAlgorithm().getX() + lastChildPE.getGraphicsAlgorithm().getWidth() - 
//                             firstChildPE.getGraphicsAlgorithm().getX();
//
//            int above = findBiggestWidthInPartTreeAbove(next);
//            boolean isCentered = nextGA.getX() == firstChildPE.getGraphicsAlgorithm().getX() + (childWidth - nextGA.getWidth()) / 2;
////            System.out.println("N: " + next + ", A: " + above + ", CW: " + childWidth);
////            System.out.println("X: " + nextGA.getX() + ", CHX: " + (firstChildPE.getGraphicsAlgorithm().getX() + (childWidth - nextGA.getWidth()) / 2));
//            if(above < childWidth && !isCentered)
//            {
//               xStart = firstChildPE.getGraphicsAlgorithm().getX();
//               
////               if(nextGA.getX() <= xStart) {
////                  xMargin = (childWidth - nextGA.getWidth()) / 2;
////               }
//
//   //            System.out.println("XM: " + xMargin + ", XS: " + xStart + ", NPEX: " + nextPE.getGraphicsAlgorithm().getX());
//               
//               // Make sure that the new position is not "lefter" as the old one because this area is reserved for the previous branch and they should not collapse  
//               if (xMargin + xStart < nextGA.getX()) {
//                  
//                  if(!isMC || !mc.isCollapsed())
//                  {
//                     // Collapse possible, so keep old xStart 
//                     xMargin = 0;
//                     xStart = nextGA.getX();
//                     removeChildrenRequired = true;  
//                  }
//               }
//               
//               maxWidth = childWidth;
//            }
//            else if(above > childWidth || above > -1 && above < childWidth && isCentered)
//            {
//               xStart = nextGA.getX() - (above - nextGA.getWidth()) / 2;
//               move = -firstChildPE.getGraphicsAlgorithm().getX() + (nextGA.getWidth() - childWidth) / 2;
//            }
//         }
//         
////         System.out.println("XM: " + xMargin + ", XS: " + xStart + ", X: " + nextPE.getGraphicsAlgorithm().getX());
//         
//         // Go back to root or branch split and collect descendants while computing max width
//         // If a parent node has more than one child it is treated as leaf node in a further iteration by adding it to leafs
//         List<PictogramElement> descendantsPE = new LinkedList<PictogramElement>();
//         
//         ISEDDebugNode current = next;
//         PictogramElement currentPE = nextPE;
//
//         if(isMC && !mc.isCollapsed()) {
//            descendantsPE.add(getPictogramElementForBusinessObject(current, 0));
//         }
//         
//         boolean locked = false;
//         
////         boolean startReached = false;
//         do {
//            currentPE = getPictogramElementForBusinessObject(current);
//            
////            System.out.println("Current: " + current);
////            if(!startReached) {
//               doneNodes.add(current); // Mark element as centered because it will be done before the next leaf node will be treated in outer most loop
//               descendantsPE.add(currentPE);
////            }
//
//            int currentWidth = currentPE.getGraphicsAlgorithm().getWidth();
//            if (currentWidth > maxWidth && (!locked || removeChildrenRequired)) {
//               maxWidth = currentWidth;          
//            }
//            
//            ISEDDebugNode child = current;
//            current = NodeUtil.getParent(child);
////            System.out.println("N: " + next + ", C: " + current);
////            if(current == start) {
////               startReached = true;
////            }
//
//            if (current != null && NodeUtil.getChildren(current).length != 1) {
//               if(doneNodes.containsAll(new HashSet<ISEDDebugNode>(Arrays.asList(NodeUtil.getChildren(current))))){
////               if (ArrayUtil.isLast(NodeUtil.getChildren(current), child)) {  // Update parent only if all of his branches are correctly centered
//                  leafs.add(current);
////                  System.out.println("C2: " + current);
//               }
////               
////               int above = findBiggestWidthInPartTreeAbove(current);
////               
////               if(above > maxWidth + OFFSET) {
////                  System.out.println("AW: " + above + ", MW: " + maxWidth + ", C: " + current);
////                  GraphicsAlgorithm gandalf = getPictogramElementForBusinessObject(NodeUtil.getParent(next)).getGraphicsAlgorithm();
//////                  xStart = gandalf.getX();
//////                  maxWidth = -2 * xStart + 2 * gandalf.getX() + gandalf.getWidth() - OFFSET;
////                  nextGA.setX(gandalf.getX() + (gandalf.getWidth() - nextGA.getWidth()) / 2);
////                  locked = true;
////               }
//               
//               current = null;
//            }
//         } while (current != null && !monitor.isCanceled());
//
//         // Center collected descendants based on the computed maximal element width
//         Iterator<PictogramElement> descendantIter = descendantsPE.iterator();
//         while (descendantIter.hasNext() && !monitor.isCanceled()) {
//            PictogramElement pe = descendantIter.next();
//            GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
//            int newX = xMargin + xStart + xOff + (maxWidth - ga.getWidth()) / 2;
////            System.out.println("OLDX: " + ga.getX());
//            ga.setX(newX);
////            System.out.println("NEWX: " + newX);
//
//            ISEDDebugNode node = (ISEDDebugNode) getBusinessObjectForPictogramElement(pe);
//
//            if(NodeUtil.getChildren(node).length > 1 && move != 0)
//            {
//               move = ga.getX() + move;
//               ga.setX(ga.getX() - move);
//               moveSubTreeHorizontal(node, move, monitor);
//
//               if(node instanceof ISEDMethodCall) {
//                  GraphicsAlgorithm rectGA = getPictogramElementForBusinessObject(node, 0).getGraphicsAlgorithm();
//                  rectGA.setX(rectGA.getX() - move);
//               }
//            }
//         }
//         
//         monitor.worked(1);
//         // Center children again if required
//         if (removeChildrenRequired && !ArrayUtil.isEmpty(NodeUtil.getChildren(next))) {
//            ISEDDebugNode lastChild = ArrayUtil.getLast(NodeUtil.getChildren(next));
//            int mostRightX = findMostRightXInSubtree(lastChild);
//            int offset = (maxWidth - (mostRightX - xStart)) / 2;
//            // Center children again only if offset is positive, because otherwise an overlap with the branch next to the left is possible
//            if (offset > 0) {
//               SEDPreorderIterator iter = new SEDPreorderIterator(next);
//               while (iter.hasNext()) {
//                  ISEDDebugElement nextChild = iter.next();
//                  if (nextChild != next) {
//                     PictogramElement nextChildPE = getPictogramElementForBusinessObject(nextChild);
//                     if (nextChildPE != null) {
//                        nextChildPE.getGraphicsAlgorithm().setX(nextChildPE.getGraphicsAlgorithm().getX() + offset);
//                     }
//                  }
//               }
//               
//               if(!ArrayUtil.isEmpty(next.getCallStack())) {
//                  PictogramElement mcPE = getPictogramElementForBusinessObject(next.getCallStack()[0], 0);
//                  mcPE.getGraphicsAlgorithm().setX(mcPE.getGraphicsAlgorithm().getX() + offset);
//               }
//            }
//         }
//      }
//   }
   
   /**
    * TODO
    * @throws DebugException 
    */
   protected void adjustRects(ISEDDebugNode node, IProgressMonitor monitor) throws DebugException {
      ISEDIterator iter = new SEDPreorderIterator(node);
      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();
         
         if(next instanceof ISEDDebugNode) {
            compute((ISEDDebugNode) next, monitor);
         }
      }
   }
   
   /*
    * TODO
    */
   private void compute(ISEDDebugNode node, IProgressMonitor monitor) throws DebugException {
      PictogramElement pe = getPictogramElementForBusinessObject(node);
      
      if(pe == null) {
         return;
      }
      
      GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
      
      if(!ArrayUtil.isEmpty(node.getCallStack()))
      {
         ISEDDebugNode mc = node.getCallStack()[0];
         PictogramElement mcPE = getPictogramElementForBusinessObject(mc, 0);
         GraphicsAlgorithm mcGA = mcPE.getGraphicsAlgorithm();
         
         if(node instanceof ISEDMethodCall)
         {
            GraphicsAlgorithm rectGA = getPictogramElementForBusinessObject(node, 0).getGraphicsAlgorithm();
            if(rectGA.getX() <= mcGA.getX()) {
               moveSubTreeHorizontal(node, METOFF, monitor);
               int mostLeft = findMostLeftXInMethod(node) - METOFF;
//               int mostLeft = findMostLeftXInMethod(NodeUtil.getChildren(node)[0]);
//               System.out.println("ML: " + mostLeft + ", X: " + rectGA.getX());
               if(mostLeft > -1 && mostLeft < rectGA.getX()) {
                  int toMove = rectGA.getX() - mostLeft;
                  moveSubTreeHorizontal(node, toMove, monitor);
                  updateParents(pe, toMove, monitor);
//                  moveRighterNodes(node, 100, monitor);
                  
                  rectGA.setX(rectGA.getX() - toMove);
               }
               else if(mostLeft > rectGA.getX()) {
//                  mostLeft -= METOFF;
                  rectGA.setWidth(rectGA.getWidth() + rectGA.getX() - mostLeft);
                  rectGA.setX(mostLeft);
               }

               updateParents(pe, METOFF, monitor);
            }
            
            int mostRightInPrev = findMostRightXInPreviousBranch(node);

            if(mostRightInPrev > -1)
            {
               if(rectGA.getX() < mostRightInPrev + OFFSET)
               {
                  int toMove = mostRightInPrev + OFFSET - rectGA.getX();
                  moveRightAndAbove(node, toMove, monitor);
                  moveSubTreeHorizontal(node, toMove, monitor);
               }
               
               updateAllMethodRectWidths((ISEDMethodCall) node, ga);
            }
            
            ga = rectGA;
         }

         if(ga.getX() < mcGA.getX() + METOFF)
         {
            if(!ArrayUtil.isEmpty(mc.getCallStack()))
            {
               ISEDDebugNode outerMethod = mc.getCallStack()[0];
               PictogramElement outerPE = getPictogramElementForBusinessObject(outerMethod, 0);
               GraphicsAlgorithm outerGA = outerPE.getGraphicsAlgorithm();
//               System.out.println("Node: " + node);
//               System.out.println("OX: " + (outerGA.getX() + METOFF) + ", IX: " + mcGA.getX() + ", X: " + ga.getX());
               if(outerGA.getX() + METOFF <= mcGA.getX())
               {
                  // The new Node overlaps the own Method and the parent Method
                  if(ga.getX() < outerGA.getX() + METOFF) {
                     int toMove = outerGA.getX() + METOFF - ga.getX();
                     moveRightAndAbove(node, toMove, monitor);
                     moveSubTreeHorizontal(node, toMove, monitor);
                  }
                  // The new Node just overlaps the own Method
                  else {
                     // The Node lies in the offset of the parent Method
                     if(ga.getX() - METOFF <= outerGA.getX() + METOFF) {
                        int toMove = outerGA.getX() + METOFF - (ga.getX() - METOFF);
                        moveRightAndAbove(node, toMove, monitor);
                        moveSubTreeHorizontal(node, toMove, monitor);
                        mcGA.setX(outerGA.getX() + METOFF);
                     }
                     else {
                        int mostRightInPrev = findMostRightXInPreviousBranch(node);
                        
                        if(mostRightInPrev > outerGA.getX() + METOFF && mostRightInPrev + OFFSET <= mcGA.getX())
                        {
                           int toMove = mcGA.getX() + METOFF - ga.getX();
                           
                           if(mcGA.getX() - METOFF > mostRightInPrev) {
                              mcGA.setX(mcGA.getX() - toMove);
                           }
                           else {
                              moveRightAndAbove(node, toMove, monitor);
                              moveSubTreeHorizontal(node, toMove, monitor);
                           }
                        }
                        else {
                           if(outerGA.getX() + METOFF /* + OFFSET */ <= ga.getX()) {
                              if(outerGA.getX() + METOFF <= ga.getX() - METOFF) {
                                 mcGA.setX(ga.getX() - METOFF);
                              }
                              else {
                                 int toMove = METOFF - ga.getX();
                                 moveRightAndAbove(node, toMove, monitor);
                                 moveSubTreeHorizontal(node, toMove, monitor);
                                 mcGA.setX(outerGA.getX() + METOFF);
                              }
                           }
                        }

//                        if(mostRightInPrev > -1 && mostRightInPrev + OFFSET <= mcGA.getX()) {
//                           int toMove = mcGA.getX() + METOFF - ga.getX();
//                           moveRightAndAbove(node, toMove, monitor);
//                           moveSubTreeHorizontal(node, toMove, monitor);
//                        }
//                        else {
//                           if(mostRightInPrev == -1) {
//                              mostRightInPrev = outerGA.getX() + METOFF;
//                           }
//                           
//                           if(mostRightInPrev + OFFSET <= ga.getX()) {
//                              if(mostRightInPrev + OFFSET <= ga.getX() - METOFF) {
//                                 mcGA.setX(ga.getX() - METOFF);
//                              }
//                              else {
//                                 int toMove = METOFF - ga.getX();
//                                 moveRightAndAbove(node, toMove, monitor);
//                                 moveSubTreeHorizontal(node, toMove, monitor);
//                                 mcGA.setX(mostRightInPrev + OFFSET);
//                              }
//                           }
//                        }
                     }
                  }
               }
            }
            else if(node instanceof ISEDMethodCall || node instanceof ISEDBaseMethodReturn) {
               int toMove = mcGA.getX() + METOFF - ga.getX();
               moveRightAndAbove(node, toMove, monitor);
               moveSubTreeHorizontal(node, toMove, monitor);
            }
            
//            updateParents(pe, METOFF, monitor);
         }
         
         ISEDDebugNode mostRightNode = findMostRightNodeInMethod(mc);
         if(mostRightNode != null) {
            updateAllMethodRectWidths((ISEDMethodCall) mc, getPictogramElementForBusinessObject(mostRightNode).getGraphicsAlgorithm());
         }
      }
   }

   /**
    * The sub tree of the given {@link PictogramElement} may overlap
    * with other branches on the right sight. This method moves all branches
    * right to the given {@link PictogramElement} to the right and re-centers
    * the parent nodes.
    * @param pictogramElement The {@link PictogramElement} which was updated.
    * @param offsetBetweenPictogramElements The offset between {@link PictogramElement}s.
    * @param monitor The {@link IProgressMonitor} to use.
    * @return {@code true}, if update process was successful
    * @throws DebugException Occurred Exception.
    */
   protected boolean updateParents(PictogramElement pictogramElement, 
                                   int offsetBetweenPictogramElements,
                                   IProgressMonitor monitor) throws DebugException {
      monitor.beginTask("Update parents", IProgressMonitor.UNKNOWN);
      try {
         if (!monitor.isCanceled()) {
            Object[] bos = getAllBusinessObjectsForPictogramElement(pictogramElement);
            int i = 0;
            while (i < bos.length && !monitor.isCanceled()) {
               if (bos[i] instanceof ISEDDebugNode) {
                  ISEDDebugNode node = (ISEDDebugNode)bos[i];
                  ISEDDebugNode parent = NodeUtil.getParent(node);
                  if (parent != null) {
                     
                     // Find most left node in righter nodes
                     int mostLeftFollowing = findMostLeftXInFollowingBranch(node);
//                     PictogramElement mostLeftSiblingPE = findMostLeftSiblingPE(node);
//                     if (mostLeftSiblingPE != null) {
                     if(mostLeftFollowing > - 1) {
//                     System.out.println("ML: " + mostLeft + ", SL: " + mostLeftSiblingPE.getGraphicsAlgorithm().getX());
//                        System.out.println(getBusinessObjectForPictogramElement(mostLeftSiblingPE));
                        // Compute maximal branch x and width
                        int maxXOnParents = findMostRightXOfBranchInParents(node);
                        int maxXInChildren = findMostRightXInSubtree(node);
                        int maxXOfBranch = maxXOnParents > maxXInChildren ? maxXOnParents : maxXInChildren; 
                        // Compute distance to move righter nodes
                        int distance = maxXOfBranch + offsetBetweenPictogramElements - mostLeftFollowing;//mostLeftSiblingPE.getGraphicsAlgorithm().getX();
                        if (distance != 0) {
//                           System.out.println(node + ", Sib: " + getBusinessObjectForPictogramElement(mostLeftSiblingPE));
                           // Move righter nodes by the given distance
//                           System.out.println("MXB: " + maxXOfBranch + ", DIS: " + distance + ", MLX: " + mostLeftFollowing);
                           moveRighterNodes(node, distance, monitor);
                        }
                     }
                  }
               }
               i++;
            }
         }
         return true;
      }
      finally {
         monitor.done();
      }
   }
   
   /**
    * TODO
    * @throws DebugException 
    */
   protected void updateAllMethodRectHeights(ISEDMethodCall mc, GraphicsAlgorithm ga, boolean isMethodReturn) throws DebugException {
      int methodMaxY = ga.getY() + ga.getHeight() + (isMethodReturn ? -ga.getHeight() / 2 : OFFSET);

      do
      {
         GraphicsAlgorithm mcGA = getPictogramElementForBusinessObject(mc, 0).getGraphicsAlgorithm();
         
         ISEDBranchCondition[] bcs = ((ISEDMethodCall) mc).getMethodReturnConditions();
         
         // Need for inner Method, Fail for outer Method
         for(int i = 0; i < bcs.length; i++) {
            ISEDDebugNode mr = bcs[i].getChildren()[0];
            PictogramElement mrPE = getPictogramElementForBusinessObject(mr);
            
            if(mrPE != null) {
               GraphicsAlgorithm mrGA = mrPE.getGraphicsAlgorithm();
               if(mrGA.getY() + mrGA.getHeight() / 2 > methodMaxY) {
                  methodMaxY = mrGA.getY() + mrGA.getHeight() / 2; 
               }
            }
         }

         if(methodMaxY > mcGA.getY() + mcGA.getHeight())
         {
            mcGA.setHeight(methodMaxY - mcGA.getY());
            
            // Pushes the nodes down to the end of the Methodrect
            for(int i = 0; i < bcs.length; i++) {
               ISEDDebugNode mr = bcs[i].getChildren()[0];
               PictogramElement mrPE = getPictogramElementForBusinessObject(mr);
               
               if(mrPE != null) {
                  int diff = mcGA.getY() + mcGA.getHeight() - mrPE.getGraphicsAlgorithm().getY() -  mrPE.getGraphicsAlgorithm().getHeight() / 2;
                  moveSubTreeVertical(mr, diff);
               }
            }
         }
            
         if(isMethodReturn) {
            ga.setY(mcGA.getY() + mcGA.getHeight() - ga.getHeight() / 2);
            
            int deepestY = findDeepestYInMethod(mc);
            if(mcGA.getY() + mcGA.getHeight() - ga.getHeight() / 2 - deepestY < OFFSET) {
               for(int i = 0; i < bcs.length; i++) {
                  ISEDDebugNode mr = bcs[i].getChildren()[0];
                  PictogramElement mrPE = getPictogramElementForBusinessObject(mr);
                  
                  if(mrPE != null) {
                     moveSubTreeVertical(mr, OFFSET);
                  }
               }
               mcGA.setHeight(mcGA.getHeight() + OFFSET);
            }
         }
         
         methodMaxY = mcGA.getY() + mcGA.getHeight() + ga.getHeight() + OFFSET;// + (isMethodReturn ? - ga.getHeight() / 2 : 0);
         
         mc = !ArrayUtil.isEmpty(mc.getCallStack()) ? (ISEDMethodCall) mc.getCallStack()[0] : null;
         isMethodReturn = false;
      } while(mc != null);
   }
   
   /**
    * TODO
    * @throws DebugException 
    */
   protected void updateAllMethodRectWidths(ISEDMethodCall mc, GraphicsAlgorithm peGA) throws DebugException {
      int methodMaxX = peGA.getX() + peGA.getWidth() + METOFF;
      GraphicsAlgorithm mcGA;
//      System.out.println("MC:" + mc);
      do
      {
//         PictogramElement mcPE = getPictogramElementForBusinessObject(node, 0);
         mcGA = getPictogramElementForBusinessObject(mc, 0).getGraphicsAlgorithm();
//         System.out.println("Node:" + mc);
//         int mostLeft = findMostLeftXInMethod(mc);
//         System.out.println("MX:" + methodMaxX + ", X: " + (mcGA.getX() + METOFF));
//         if(mostLeft > mcGA.getX() + METOFF && !ArrayUtil.isEmpty(mc.getCallStack())) {
//            mcGA.setX(mostLeft - METOFF);
//            mcGA.setWidth(mcGA.getWidth() - (mostLeft - mcGA.getX() + METOFF));
//         }
         if(methodMaxX > mcGA.getX() + mcGA.getWidth()) {
            int diff = methodMaxX - mcGA.getX() - mcGA.getWidth();
            mcGA.setWidth(mcGA.getWidth() + diff);
         }
         
         methodMaxX = mcGA.getX() + mcGA.getWidth() + METOFF;
         mc = !ArrayUtil.isEmpty(mc.getCallStack()) ? (ISEDMethodCall) mc.getCallStack()[0] : null;
      } while(mc != null);
//      System.out.println("??");
   }
   
   protected int findBiggestWidthInPartTreeAbove(ISEDDebugNode start) throws DebugException {
      ISEDDebugNode node = start;
      int width = -1;
      do
      {
         node = NodeUtil.getParent(node);
         if(node == null || NodeUtil.getChildren(node).length != 1 && width > -1) {
            break;
         }
         
         PictogramElement nodePE = getPictogramElementForBusinessObject(node);
         if(nodePE != null)
         {
            GraphicsAlgorithm nodeGA = nodePE.getGraphicsAlgorithm();
            if(nodeGA.getWidth() > width || width == -1) {
               width = nodeGA.getWidth();
            }
         }
      } while(true);
      return width;
   }

   /**
    * Searches the sibling node which is X coordinate is more to the right
    * and which is the one which is most left of all siblings.
    * @param node The {@link ISEDDebugNode} to search in.
    * @return The found {@link PictogramElement} or {@code null} if no one was found.
    * @throws DebugException Occurred Exception.
    */
   protected PictogramElement findMostLeftSiblingPE(ISEDDebugNode node) throws DebugException {
      PictogramElement sibling = null;
      if (node != null) {
         ISEDDebugNode parent = NodeUtil.getParent(node);
         while (parent != null && sibling == null) {
            ISEDDebugNode[] siblings = NodeUtil.getChildren(parent);
            int index = ArrayUtil.indexOf(siblings, node);
            if (index < 0) {
               throw new DebugException(LogUtil.getLogger().createErrorStatus("Child \"" + node + "\" is not contained in parent's children \"" + Arrays.toString(siblings) + "\"."));
            }
            if (index < siblings.length - 1) {
               sibling = findMostLeftNodePE(siblings[index + 1]);
            }
            else {
               node = parent;
               parent = NodeUtil.getParent(node);
            }
         }
      }
      return sibling;
   }
   
   /**
    * Searches the node in the subtree starting at the given {@link ISEDDebugNode}
    * which has the X coordinate most left.
    * @param node The {@link ISEDDebugNode} to search in.
    * @return The found {@link PictogramElement} of the most left node or {@code null} if no one was found.
    * @throws DebugException Occurred Exception.
    */
   protected PictogramElement findMostLeftNodePE(ISEDDebugNode node) throws DebugException {
      // Compute initial left position
      ISEDDebugNode mostLeft = node;
      PictogramElement mostLeftPE = getPictogramElementForBusinessObject(mostLeft);
      // Iterate over most left sub trees
      while (node != null) {
         // Check if the current node is more left
         PictogramElement nodePE = getPictogramElementForBusinessObject(node);
         if (nodePE != null && nodePE.getGraphicsAlgorithm().getX() < mostLeftPE.getGraphicsAlgorithm().getX()) {
            mostLeft = node;
            mostLeftPE = nodePE;
         }
         // Change node for next loop iteration
         ISEDDebugNode[] children = NodeUtil.getChildren(node);
         if (!ArrayUtil.isEmpty(children)) {
            node = children[0];
         }
         else {
            node = null;
         }
      }
      return mostLeftPE;
   }

   /**
    * Iterates over the parents of the given {@link ISEDDebugNode} until
    * the beginning of the branch is reached and computes the x value
    * of the most left visited {@link ISEDDebugNode}.
    * @param node The {@link ISEDDebugNode} to start.
    * @return The most left x value of parent {@link ISEDDebugNode}s in the same branch.
    * @throws DebugException Occurred Exception.
    */
   protected int findMostLeftXOfBranchAbove(ISEDDebugNode node) throws DebugException {
      int mostLeftXInBranch = 0;
      boolean mostLeftXInBranchInitialized = false;
      while (node != null) {
         PictogramElement pe = getPictogramElementForBusinessObject(node);
         if (pe != null) {
            if (mostLeftXInBranchInitialized) {
               if (pe.getGraphicsAlgorithm().getX() < mostLeftXInBranch) {
                  mostLeftXInBranch = pe.getGraphicsAlgorithm().getX();
//                  System.out.println("Node: " + node + ", X: " + mostLeftXInBranch);
               }
            }
            else {
               mostLeftXInBranch = pe.getGraphicsAlgorithm().getX();
               mostLeftXInBranchInitialized = true;
            }
         }        
         
         // Select parent for next loop iteration
         ISEDDebugNode child = node;
         node = NodeUtil.getParent(node);
         if (node != null && NodeUtil.getChildren(node).length != 1) {
//         if (node != null && NodeUtil.getChildren(node).length != 1 && !ArrayUtil.isFirst(NodeUtil.getChildren(node), child)) {
            node = null;
         }
      }
      return mostLeftXInBranch;
   }
   
   protected int findMostLeftXOfBranchInParents(ISEDDebugNode node) throws DebugException {
      int mostLeftXInBranch = 0;
      boolean mostLeftXInBranchInitialized = false;
      while (node != null) {
         PictogramElement pe = getPictogramElementForBusinessObject(node);
//         PictogramElement pe = node instanceof ISEDMethodCall ? getPictogramElementForBusinessObject(node, 0) : getPictogramElementForBusinessObject(node);
         if (pe != null) {
            if (mostLeftXInBranchInitialized) {
               if (pe.getGraphicsAlgorithm().getX() < mostLeftXInBranch) {
                  mostLeftXInBranch = pe.getGraphicsAlgorithm().getX();
//                  System.out.println("Node: " + node + ", X: " + mostLeftXInBranch);
               }
            }
            else {
               mostLeftXInBranch = pe.getGraphicsAlgorithm().getX();
               mostLeftXInBranchInitialized = true;
            }
         }        
         
         // Select parent for next loop iteration
         ISEDDebugNode child = node;
         node = NodeUtil.getParent(node);
         if (node != null && NodeUtil.getChildren(node).length != 1 && !ArrayUtil.isFirst(NodeUtil.getChildren(node), child)) {
            node = null;
         }
      }
      return mostLeftXInBranch;
   }
   
   /**
    * TODO
    * @param node
    * @return
    * @throws DebugException
    */
   protected int findMostLeftXInPreviousBranch(ISEDDebugNode node) throws DebugException {
      do
      {
         ISEDDebugNode parent = NodeUtil.getParent(node);
         
         if(parent == null) {
            return -1;
         }
         
//         if(parent instanceof ISEDMethodCall) {
//            return getPictogramElementForBusinessObject(parent, 0).getGraphicsAlgorithm().getX() + METOFF;
//         }

         ISEDDebugNode[] children = NodeUtil.getChildren(parent);
         
         if(!ArrayUtil.isFirst(children, node)) {
            return findMostLeftXInSubtree(ArrayUtil.getPrevious(NodeUtil.getChildren(NodeUtil.getParent(node)), node));
         }
         
         node = parent;
      } while(true);
   }
   
   /**
    * TODO
    * @param node
    * @return
    * @throws DebugException
    */
   protected int findMostLeftXInFollowingBranch(ISEDDebugNode node) throws DebugException {
      do
      {
         ISEDDebugNode parent = NodeUtil.getParent(node);
         
         if(parent == null) {
            return -1;
         }

         ISEDDebugNode[] children = NodeUtil.getChildren(parent);
         
         if(!ArrayUtil.isLast(children, node)) {
            return findMostLeftXInSubtree(ArrayUtil.getFollowing(NodeUtil.getChildren(NodeUtil.getParent(node)), node));
         }
         
         node = parent;
      } while(true);
   }
   
   /**
    * TODO
    * @param node
    * @return
    * @throws DebugException
    */
   protected ISEDDebugNode findMostLeftXNodeInParentBranches(ISEDDebugNode node) throws DebugException {
//      int mostLeftXInBranch = -1;
      ISEDDebugNode mostLeftNode = null;
      while (node != null) {
         PictogramElement pe = getPictogramElementForBusinessObject(node);
         if (pe != null) {
//            System.out.println(node);
//            System.out.println("NX: " + pe.getGraphicsAlgorithm().getWidth() + ", OX: " + (mostLeftNode == null ? 0 : getPictogramElementForBusinessObject(mostLeftNode).getGraphicsAlgorithm().getWidth()));
//            if (mostLeftNode == null || pe.getGraphicsAlgorithm().getWidth() > getPictogramElementForBusinessObject(mostLeftNode).getGraphicsAlgorithm().getWidth()) {
            if (mostLeftNode == null || pe.getGraphicsAlgorithm().getX() < getPictogramElementForBusinessObject(mostLeftNode).getGraphicsAlgorithm().getX()) {
               mostLeftNode = node;
            }
         }        
         
         // Select parent for next loop iteration
         ISEDDebugNode child = node;
         node = NodeUtil.getParent(node);
//         if (node != null && NodeUtil.getChildren(node).length != 1 && ArrayUtil.isFirst(NodeUtil.getChildren(node), child)) {
//            node = null;
//         }
      }
      return mostLeftNode;
//      GraphicsAlgorithm ga = null;
//      while (node != null) {
//         PictogramElement pe = getPictogramElementForBusinessObject(node);
//         if (pe != null) {
//            if (pe.getGraphicsAlgorithm().getX() < mostLeftXInBranch || mostLeftXInBranch == -1) {
//               mostLeftXInBranch = pe.getGraphicsAlgorithm().getX();
//            }
//         }        
//         
//         // Select parent for next loop iteration
//         ISEDDebugNode child = node;
//         node = NodeUtil.getParent(node);
//         if (node != null && NodeUtil.getChildren(node).length != 1 && !ArrayUtil.isLast(NodeUtil.getChildren(node), child)) {
//            node = null;
//         }
//      }
//      return mostLeftXInBranch;
//      int mostLeftXInBranch = -1;
//      do
//      {
//         ISEDDebugNode parent = NodeUtil.getParent(node);
//         
//         if(parent == null) {
//            return mostLeftXInBranch;
//         }
//
//         if(NodeUtil.getChildren(parent).length != 1) {
//            while (parent != null) {
//               PictogramElement pe = getPictogramElementForBusinessObject(parent);
//               if (pe != null) {
//                  if (pe.getGraphicsAlgorithm().getX() < mostLeftXInBranch || mostLeftXInBranch == -1) {
//                     mostLeftXInBranch = pe.getGraphicsAlgorithm().getX();
//                  }
//               }
//               
//               // Select parent for next loop iteration
//               parent = NodeUtil.getParent(parent);
//               if (parent != null && NodeUtil.getChildren(parent).length != 1) {
//                  parent = null;
//               }
//            }
//            return mostLeftXInBranch;
//         }
//         
//         node = parent;
//      } while(true);
   }
   
   /**
    * Iterates over the most left children of the given {@link ISEDDebugNode}
    * and computes the minimal x value of the visited child {@link ISEDDebugNode}s.
    * @param node The {@link ISEDDebugNode} to start.
    * @return The most minimal x value of most left child {@link ISEDDebugNode}s.
    * @throws DebugException Occurred Exception.
    */
   protected int findMostLeftXInSubtree(ISEDDebugNode node) throws DebugException {
      int mostLeftXInSubtree = 0;
      boolean mostLeftXInSubtreeInitialized = false;
      while (node != null) {
         PictogramElement pe = node instanceof ISEDMethodCall ? getPictogramElementForBusinessObject(node, 0) : getPictogramElementForBusinessObject(node);
         if (pe != null) {
            if (mostLeftXInSubtreeInitialized) {
               if (pe.getGraphicsAlgorithm().getX() < mostLeftXInSubtree) {
                  mostLeftXInSubtree = pe.getGraphicsAlgorithm().getX();
               }
            }
            else {
               mostLeftXInSubtree = pe.getGraphicsAlgorithm().getX();
               mostLeftXInSubtreeInitialized = true;
            }
         }
         // Select child for next loop iteration
         node = ArrayUtil.getFirst(NodeUtil.getChildren(node));
      }
      return mostLeftXInSubtree;
   }
   
   protected int findMostLeftXInMethod(ISEDDebugNode node) throws DebugException {
      int mostLeftXInSubtree = -1;
      ISEDDebugNode mc = node;
      while (node != null) {
         if(!node.equals(mc)) {
//         System.out.println("Node: " + node + ", MC: " + mc + ", E?: " + (node instanceof ISEDMethodCall && !node.equals(mc)));
         PictogramElement pe = (node instanceof ISEDMethodCall && !node.equals(mc)) ? getPictogramElementForBusinessObject(node, 0) : getPictogramElementForBusinessObject(node);
         if (pe != null) {
            GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
            if (ga.getX() < mostLeftXInSubtree || mostLeftXInSubtree == -1) {
               mostLeftXInSubtree = ga.getX();
            }
         }
         }
         // Select child for next loop iteration
         ISEDDebugNode parent = node;
         node = ArrayUtil.getFirst(NodeUtil.getChildren(node));
//         System.out.println("Node: " + parent + ", Child: " + node);
         if(node != null && ArrayUtil.isEmpty(node.getCallStack()) && !(node instanceof ISEDBranchCondition)
               || parent instanceof ISEDMethodReturn && parent.getCallStack()[0].equals(mc)) {
            node = null;
         }
      }
      return mostLeftXInSubtree;
   }
   
   protected ISEDDebugNode findMostRightNodeInMethod(ISEDDebugNode node) throws DebugException {
      int mostRightXInSubtree = -1;
      ISEDDebugNode mostRightNode = null;
      ISEDDebugNode mc = node;
      while (node != null) {
         if(!node.equals(mc)) {
            PictogramElement pe = (node instanceof ISEDMethodCall && !node.equals(mc)) ? getPictogramElementForBusinessObject(node, 0) : getPictogramElementForBusinessObject(node);
            if (pe != null) {
               GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
               if (ga.getX() + ga.getWidth() > mostRightXInSubtree || mostRightXInSubtree == -1) {
                  mostRightXInSubtree = ga.getX() + ga.getWidth();
                  mostRightNode = node;
               }
            }
         }
         // Select child for next loop iteration
         ISEDDebugNode parent = node;
         node = ArrayUtil.getLast(NodeUtil.getChildren(node));
         if(node != null && ArrayUtil.isEmpty(node.getCallStack()) && !(node instanceof ISEDBranchCondition)
               || parent instanceof ISEDMethodReturn && parent.getCallStack()[0].equals(mc)) {
            node = null;
         }
      }
      return mostRightNode;
   }

   /**
    * Iterates over the parents of the given {@link ISEDDebugNode} until
    * the beginning of the branch is reached and computes the maximal x value
    * (x + width) of the visited {@link ISEDDebugNode}s.
    * @param node The {@link ISEDDebugNode} to start.
    * @return The most maximal x value of parent {@link ISEDDebugNode}s in the same branch.
    * @throws DebugException Occurred Exception.
    */
   protected int findMostRightXOfBranchInParents(ISEDDebugNode node) throws DebugException {
      int mostRightXInBranch = 0;
      boolean mostRightXInBranchInitialized = false;
      while (node != null) {
         PictogramElement pe = node instanceof ISEDMethodCall ? getPictogramElementForBusinessObject(node, 0) : getPictogramElementForBusinessObject(node);
         if (pe != null) {
            if (mostRightXInBranchInitialized) {
               if (pe.getGraphicsAlgorithm().getX() + pe.getGraphicsAlgorithm().getWidth() > mostRightXInBranch) {
                  mostRightXInBranch = pe.getGraphicsAlgorithm().getX() + pe.getGraphicsAlgorithm().getWidth();
//                  System.out.println("MRX: " + node + ", X: " + mostRightXInBranch);
               }
            }
            else {
               mostRightXInBranch = pe.getGraphicsAlgorithm().getX() + pe.getGraphicsAlgorithm().getWidth();
               mostRightXInBranchInitialized = true;
//               System.out.println("MRXI: " + node + ", X: " + mostRightXInBranch);
            }
         }
         // Select parent for next loop iteration
         ISEDDebugNode child = node;
         node = NodeUtil.getParent(node);

         if (node != null && NodeUtil.getChildren(node).length != 1 && !ArrayUtil.isLast(NodeUtil.getChildren(node), child)) {
            node = null;
         }
      }
      return mostRightXInBranch;
   }

   /**
    * Iterates over the most right children of the given {@link ISEDDebugNode}
    * and computes the maximal x value (x + width) of the visited child {@link ISEDDebugNode}s.
    * @param node The {@link ISEDDebugNode} to start.
    * @return The most maximal x value of most right child {@link ISEDDebugNode}s.
    * @throws DebugException Occurred Exception.
    */
   protected int findMostRightXInSubtree(ISEDDebugNode node) throws DebugException {
      int mostRightXInSubtree = 0;
      boolean mostRightXInSubtreeInitialized = false;
      while (node != null) {
         PictogramElement pe = node instanceof ISEDMethodCall ? getPictogramElementForBusinessObject(node, 0) : getPictogramElementForBusinessObject(node);
         if (pe != null) {
            if (mostRightXInSubtreeInitialized) {
               if (pe.getGraphicsAlgorithm().getX() + pe.getGraphicsAlgorithm().getWidth() > mostRightXInSubtree) {
                  mostRightXInSubtree = pe.getGraphicsAlgorithm().getX() + pe.getGraphicsAlgorithm().getWidth();
               }
            }
            else {
               mostRightXInSubtree = pe.getGraphicsAlgorithm().getX() + pe.getGraphicsAlgorithm().getWidth();
               mostRightXInSubtreeInitialized = true;
            }
         }
         // Select child for next loop iteration
         node = ArrayUtil.getLast(NodeUtil.getChildren(node));
      }
      return mostRightXInSubtree;
   }
   
   /**
    * TODO
    * @param node
    * @return
    * @throws DebugException
    */
   protected int findMostRightXInPreviousBranch(ISEDDebugNode node) throws DebugException {
      do
      {
         ISEDDebugNode parent = NodeUtil.getParent(node);
         
         if(parent == null) {
            return -1;
         }
         
//         if(parent instanceof ISEDMethodCall) {
//            return getPictogramElementForBusinessObject(parent, 0).getGraphicsAlgorithm().getX() + METOFF;
//         }

         ISEDDebugNode[] children = NodeUtil.getChildren(parent);
         
         if(!ArrayUtil.isFirst(children, node)) {
            return findMostRightXInSubtree(ArrayUtil.getPrevious(NodeUtil.getChildren(NodeUtil.getParent(node)), node));
         }
         
         node = parent;
      } while(true);
   }
   
   protected int findDeepestYInMethod(ISEDMethodCall mc) throws DebugException {
      int deepestY = 0;
      int methodAmount = 0;
      ISEDIterator iter = new SEDMethodPreorderIterator(mc);
      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();
         
         if(next instanceof ISEDDebugNode)
         {
            ISEDDebugNode nextNode = (ISEDDebugNode) next;
            
            if(ArrayUtil.isEmpty(nextNode.getCallStack()) && !(nextNode instanceof ISEDBranchCondition)) {
               continue;
            }
            
            if(nextNode instanceof ISEDBaseMethodReturn)
            {
               if(nextNode.getCallStack()[0].equals(mc)) {
                  continue;
               }
            }
            
            PictogramElement pe = getPictogramElementForBusinessObject(nextNode);
            if (pe != null) {
               GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
               if (ga.getY() + ga.getHeight() > deepestY) {
                  deepestY = ga.getY() + ga.getHeight();
                  
                  if(nextNode instanceof ISEDMethodReturn) {
                     nextNode = nextNode.getCallStack()[0];
                  }
                  
                  if(!ArrayUtil.isEmpty(nextNode.getCallStack())) {
                     int index = ArrayUtil.indexOf(nextNode.getCallStack(), mc);

                     if(index != -1) {
                        methodAmount = index; 
                     }
                  }
               }
            }
         }
      }
      
      return deepestY + methodAmount * OFFSET;
   }
   
   /**
    * TODO
    * @throws DebugException 
    */
   protected boolean hasInnerMethod(ISEDMethodCall mc) throws DebugException {
      ISEDIterator iter = new SEDMethodPreorderIterator(mc);
      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();
         
         if(next instanceof ISEDMethodCall && !next.equals(mc)) {
            return true;
         }
      }
      
      return false;
   }
   

   /**
    * Moves all nodes which x coordinate is more to the right as the 
    * given node by the given distance.
    * @param node The {@link ISEDDebugNode} to start moving.
    * @param distance The distance to move.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void moveRighterNodes(ISEDDebugNode node, 
                                   int distance, 
                                   IProgressMonitor monitor) throws DebugException {
      if (node != null) {
         ISEDDebugNode parent = NodeUtil.getParent(node);
         while (parent != null && !monitor.isCanceled()) {
            ISEDDebugNode[] siblings = NodeUtil.getChildren(parent);
            int index = ArrayUtil.indexOf(siblings, node);
            if (index < 0) {
               throw new DebugException(LogUtil.getLogger().createErrorStatus("Child \"" + node + "\" is not contained in parent's children \"" + Arrays.toString(siblings) + "\"."));
            }
            // Move subtree of all siblings
            for (int i = index + 1; i < siblings.length; i++) {
               moveSubTreeHorizontal(siblings[i], distance, monitor);
            }
            // Re-center parent
            ISEDDebugNode firstChild = ArrayUtil.getFirst(siblings);
            ISEDDebugNode lastChild = ArrayUtil.getLast(siblings);

            PictogramElement firstChildPE = getPictogramElementForBusinessObject(firstChild);
            PictogramElement lastChildPE = getPictogramElementForBusinessObject(lastChild);
            int childWidth = lastChildPE.getGraphicsAlgorithm().getX() + lastChildPE.getGraphicsAlgorithm().getWidth() - 
                             firstChildPE.getGraphicsAlgorithm().getX();
            
            PictogramElement parentPE = getPictogramElementForBusinessObject(parent);
            GraphicsAlgorithm parentGA = parentPE.getGraphicsAlgorithm();

            int xMargin = (childWidth - parentGA.getWidth()) / 2;
            int xStart = firstChildPE.getGraphicsAlgorithm().getX();
            
            parentGA.setX(xStart + xMargin);

            if(!ArrayUtil.isEmpty(parent.getCallStack())) {
               updateAllMethodRectWidths((ISEDMethodCall) parent.getCallStack()[0], parentGA);
            }
            // Define node for next loop iteration
            node = parent;
            parent = NodeUtil.getParent(node);
         }
      }
   }
   
   /**
    * Moves all nodes which x coordinate is more to the left as the 
    * given node by the given distance.
    * @param node The {@link ISEDDebugNode} to start moving.
    * @param distance The distance to move.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void moveLefterNodes(ISEDDebugNode node, ISEDDebugNode endNode, int distance, IProgressMonitor monitor) throws DebugException {
      boolean firstBranch = true;
      int toMove = 0;
      if (node != null) {
         ISEDDebugNode parent = NodeUtil.getParent(node);
         
         if(!ArrayUtil.isEmpty(node.getCallStack())) {
            GraphicsAlgorithm rectGA = getPictogramElementForBusinessObject(node.getCallStack()[0], 0).getGraphicsAlgorithm();
            rectGA.setX(rectGA.getX() + distance);
            
//            if(rectGA)
         }
         
         while (parent != null && parent != endNode && !monitor.isCanceled()) {
//            System.out.println("Parent: " + parent + ", End: " + endNode + ", ?: " + (parent != endNode));
            ISEDDebugNode[] siblings = NodeUtil.getChildren(parent);
            int index = ArrayUtil.indexOf(siblings, node);
            if (index < 0) {
               throw new DebugException(LogUtil.getLogger().createErrorStatus("Child \"" + node + "\" is not contained in parent's children \"" + Arrays.toString(siblings) + "\"."));
            }
            
            PictogramElement parentPE = getPictogramElementForBusinessObject(parent);
            GraphicsAlgorithm parentGA = parentPE.getGraphicsAlgorithm();
            
            if(siblings.length > 1)
            {
               if(firstBranch) {
                  moveSubTreeHorizontal(siblings[index], distance, monitor);
                  firstBranch = false;
               }
               // Move subtree of all siblings
               for (int i = index - 1; i > -1; i--) {
                  moveSubTreeHorizontal(siblings[i], distance, monitor);
               }
               // Re-center parent
//               ISEDDebugNode firstChild = ArrayUtil.getFirst(siblings);
//               ISEDDebugNode lastChild = ArrayUtil.getLast(siblings);
//
//               PictogramElement firstChildPE = getPictogramElementForBusinessObject(firstChild);
//               PictogramElement lastChildPE = getPictogramElementForBusinessObject(lastChild);
//               int childWidth = lastChildPE.getGraphicsAlgorithm().getX() + lastChildPE.getGraphicsAlgorithm().getWidth() - 
//                                firstChildPE.getGraphicsAlgorithm().getX();
//
//               int xMargin = (childWidth - parentGA.getWidth()) / 2;
//               int xStart = firstChildPE.getGraphicsAlgorithm().getX();
//               toMove = xStart + xMargin - parentGA.getX();
//               
//               parentGA.setX(xStart + xMargin);
            }

            // Define node for next loop iteration
            node = parent;
            parent = NodeUtil.getParent(node);
         }
      }
   }
   
   /**
    * TODO
    * Moves all nodes which x coordinate is more to the left as the 
    * given node by the given distance.
    * @param node The {@link ISEDDebugNode} to start moving.
    * @param distance The distance to move.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void moveONodes(ISEDDebugNode node, ISEDDebugNode endNode, int distance, IProgressMonitor monitor) throws DebugException {
      boolean firstBranch = true;
      if (node != null) {
         ISEDDebugNode parent = NodeUtil.getParent(node);
         while (parent != null && parent != endNode && !monitor.isCanceled()) {
//            System.out.println("Parent: " + parent + ", End: " + endNode + ", ?: " + (parent != endNode));
            ISEDDebugNode[] siblings = NodeUtil.getChildren(parent);
            int index = ArrayUtil.indexOf(siblings, node);
            if (index < 0) {
               throw new DebugException(LogUtil.getLogger().createErrorStatus("Child \"" + node + "\" is not contained in parent's children \"" + Arrays.toString(siblings) + "\"."));
            }

            if(siblings.length > 1)
            {
               if(firstBranch) {
                  moveSubTreeHorizontal(siblings[index], -3 * distance, monitor);
                  firstBranch = false;
               }
               // Move subtree of all siblings
               for (int i = index + 1; i < siblings.length; i++) {
                  moveSubTreeHorizontal(siblings[i], distance, monitor);
               }
            }

            // Define node for next loop iteration
            node = parent;
            parent = NodeUtil.getParent(node);
         }
      }
   }

   /**
    * Moves all nodes in the sub tree starting at the given {@link ISEDDebugNode}
    * horizontal by the given distance.
    * @param root The {@link ISEDDebugNode} to start moving.
    * @param distance The distance to move in x direction.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception
    */
   protected void moveSubTreeHorizontal(ISEDDebugNode root, 
                              int distance,
                              IProgressMonitor monitor) throws DebugException {
      ISEDIterator iter = new SEDPreorderIterator(root);
      while (iter.hasNext()) {
         ISEDDebugElement node = iter.next();
         PictogramElement pe = getPictogramElementForBusinessObject(node);
         if (pe != null) {
            GraphicsAlgorithm peGA = pe.getGraphicsAlgorithm();
            peGA.setX(peGA.getX() + distance);
            ISEDDebugNode dn = (ISEDDebugNode) node;

            if(dn instanceof ISEDMethodCall)
            {
               pe = getPictogramElementForBusinessObject(node, 0);
               if (pe != null) {
                  peGA = pe.getGraphicsAlgorithm();
                  peGA.setX(peGA.getX() + distance);
               }
            }
            
            if(!ArrayUtil.isEmpty(dn.getCallStack())) {
//               GraphicsAlgorithm mcGA = getPictogramElementForBusinessObject(dn.getCallStack()[0], 0).getGraphicsAlgorithm();
//               System.out.println("Node: " + dn + ", MX:" + (peGA.getX() + peGA.getWidth() + METOFF) + ", X: " + (mcGA.getX() + METOFF));
               updateAllMethodRectWidths((ISEDMethodCall) dn.getCallStack()[0], peGA);
            }
         }
      }
   }
   
   /**
    * Moves all nodes in the sub tree starting at the given {@link ISEDDebugNode}
    * vertical by the given distance.
    * @param root The {@link ISEDDebugNode} to start moving.
    * @param distance The distance to move in x direction.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception
    */
   protected void moveSubTreeVertical(ISEDDebugNode root, int distance) throws DebugException {
      ISEDIterator iter = new SEDPreorderIterator(root);
      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();
         PictogramElement pe = getPictogramElementForBusinessObject(next);
         if (pe != null) {
            GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
            ga.setY(ga.getY() + distance);
         }
      }
   }
   
   protected void moveCompleteTree(ISEDDebugNode root, int distance) throws DebugException {
      ISEDIterator iter = new SEDPreorderIterator(root);
      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();
         PictogramElement pe = getPictogramElementForBusinessObject(next);
         if (pe != null) {
            GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
            ga.setX(ga.getX() + distance);
            
            if(next instanceof ISEDMethodCall && !ArrayUtil.isEmpty(((ISEDMethodCall) next).getCallStack())) {
               ga = getPictogramElementForBusinessObject(next, 0).getGraphicsAlgorithm();
               ga.setX(ga.getX() + distance);
            }
         }
      }
   }
   
   protected void moveRightAndAbove(ISEDDebugNode start, int distance, IProgressMonitor monitor) throws DebugException {
      ISEDDebugNode node = start;
      do
      {
         ISEDDebugNode parent = NodeUtil.getParent(node);
         
         if(parent == null) {
            return;
         }
         
         if(NodeUtil.getChildren(parent).length > 1) {
            moveRighterNodes(node, distance, monitor);
            return;
         }

         PictogramElement parentPE = getPictogramElementForBusinessObject(parent);
         if(parentPE != null)
         {
            GraphicsAlgorithm parentGA = parentPE.getGraphicsAlgorithm();
            parentGA.setX(parentGA.getX() + distance);
            
            if(parent instanceof ISEDMethodCall && !ArrayUtil.isEmpty(start.getCallStack()) && !start.getCallStack()[0].equals(parent)) {
               parentPE = getPictogramElementForBusinessObject(parent, 0);
               parentGA = parentPE.getGraphicsAlgorithm();
               parentGA.setX(parentGA.getX() + distance);
            }
         }
         node = parent;
      } while(node != null);
   }

   /**
    * Updates the style of the given {@link PictogramElement}.
    * @param pe The {@link PictogramElement} to update.
    * @param node The {@link ISEDDebugNode} as business object of the given {@link PictogramElement}.
    * @return {@code true} successful, {@code false} not succesful.
    */
   protected boolean updateStyle(PictogramElement pe, ISEDDebugNode node) {
      if (pe instanceof Shape) {
         Shape shape = (Shape)pe;
         if (shape.getGraphicsAlgorithm() instanceof RoundedRectangle) {
            RoundedRectangle rr = (RoundedRectangle)shape.getGraphicsAlgorithm();
            ISEDAnnotation[] annotations = node.computeUsedAnnotations();
            String newStyleId = ExecutionTreeStyleUtil.computeDebugNodeStyleId(annotations);
            if (!newStyleId.equals(rr.getStyle().getId())) {
               // Replace and update style
               rr.setStyle(ExecutionTreeStyleUtil.getStyleForDebugNode(newStyleId, annotations, getDiagram()));
            }
            else {
               // Update style
               ExecutionTreeStyleUtil.getStyleForDebugNode(newStyleId, annotations, getDiagram());
            }
         }
         else if (shape.getGraphicsAlgorithm() instanceof Text) {
            Text text = (Text)shape.getGraphicsAlgorithm();
            ISEDAnnotation[] annotations = node.computeUsedAnnotations();
            String newStyleId = ExecutionTreeStyleUtil.computeDebugNodeTextStyleId(annotations);
            if (!newStyleId.equals(text.getStyle().getId())) {
               // Replace and update style
               text.setStyle(ExecutionTreeStyleUtil.getStyleForDebugNodeText(newStyleId, annotations, getDiagram()));
            }
            else {
               // Update style
               ExecutionTreeStyleUtil.getStyleForDebugNodeText(newStyleId, annotations, getDiagram());
            }
         }
      }
      return true;
   }
}