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
import org.eclipse.graphiti.mm.algorithms.Image;
import org.eclipse.graphiti.mm.algorithms.RoundedRectangle;
import org.eclipse.graphiti.mm.algorithms.Text;
import org.eclipse.graphiti.mm.pictograms.ContainerShape;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.mm.pictograms.Shape;

import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDBranchStatement;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDGroupable;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.util.ISEDIterator;
import org.key_project.sed.core.util.NodeUtil;
import org.key_project.sed.core.util.SEDGroupPreorderIterator;
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
            PictogramElement pe = context.getPictogramElement();
            Object bo = getBusinessObjectForPictogramElement(pe);
            
            if(NodeUtil.canBeGrouped(bo)) {
               ISEDGroupable groupStart = (ISEDGroupable) bo;
               if(pe.getGraphicsAlgorithm() instanceof org.eclipse.graphiti.mm.algorithms.Rectangle || groupStart.isCollapsed()) {
                  return Reason.createFalseReason();
               }
            }

            if (isNameUpdateNeeded(pe)) {
               return Reason.createTrueReason("Name is out of date.");
            }
            else {
               if (isChildrenUpdateNeeded(pe)) {
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
    * @param bo the business object
    * @return linked pictogram element.
    */
   protected PictogramElement getPictogramElementForBusinessObject(Object bo) {
      if(NodeUtil.canBeGrouped(bo)) {
         return getPictogramElementForBusinessObject(bo, 1);
      }
      
      return getPictogramElementForBusinessObject(bo, 0);
   }
   
   protected PictogramElement getPictogramElementForBusinessObject(Object bo, int i) {
      if(i < 0 || i > 1)
         return null;
      
      if(i == 0)
         return getFeatureProvider().getPictogramElementForBusinessObject(bo);

      PictogramElement[] pes = getFeatureProvider().getAllPictogramElementsForBusinessObject(bo);
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
      else if (pictogramElement instanceof ContainerShape && pictogramElement.getGraphicsAlgorithm() instanceof RoundedRectangle) {
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
            
//            if(!(pictogramElement instanceof Diagram) && !(pictogramElement.getGraphicsAlgorithm() instanceof RoundedRectangle)) {
//               pictogramElement = getPictogramElementForBusinessObject(getBusinessObjectForPictogramElement(pictogramElement));
//            }

            monitor.beginTask("Update element: " + pictogramElement, 3);

            boolean success = updateName(pictogramElement, new SubProgressMonitor(monitor, 1));
            monitor.worked(1);

            // Update children, they have the correct layout after this step
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
               
               if(node == null && bo instanceof ISEDDebugTarget)
               {
                  ISEDThread[] threads = ((ISEDDebugTarget) bo).getSymbolicThreads();
                  if (!ArrayUtil.isEmpty(threads)) {
                     node = threads[0];
                  }
               }
               
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
                  
//                  for(ISEDDebugNode leaf : leafs) {
//                     System.out.println("L: " + leaf);
//                  }
                  // Center sub tree
                  ISEDDebugNode start = bos[i] instanceof ISEDDebugNode ? (ISEDDebugNode) bos[i] : null;
                  centerChildren(leafs, monitor);
                  
                  if(start != null) {
                     adjustSubtreeIfSmaller(start, monitor);
                     adjustRects(start, monitor);
                  }
                  else if(bos[i] instanceof ISEDDebugTarget)
                  {
                     ISEDThread[] threads = ((ISEDDebugTarget) bos[i]).getSymbolicThreads();
                     if (!ArrayUtil.isEmpty(threads)) {
                        adjustRects(threads[0], monitor);
                     }
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
    * @param bo The business object to create graphical representations for.
    * @param monitor The {@link IProgressMonitor} to use.
    * @param offsetBetweenPictogramElements The offset between {@link PictogramElement}s.
    * @param initialX The initial X value which is used if no parentPE is defined.
    * @return The found leaf {@link ISEDDebugNode}s.
    * @throws DebugException Occurred Exception.
    */
   protected Set<ISEDDebugNode> updateChildrenLeftAligned(ISEDDebugElement bo, 
                                                          IProgressMonitor monitor, 
                                                          int offsetBetweenPictogramElements,
                                                          int initialX) throws DebugException {
      Set<ISEDDebugNode> leafs = new LinkedHashSet<ISEDDebugNode>();
      ISEDIterator iter = new SEDPreorderIterator(bo);
      
      if(NodeUtil.canBeGrouped(bo))
      {
         ISEDGroupable groupStart = (ISEDGroupable) bo;
         if(!groupStart.isCollapsed()){
            iter = new SEDGroupPreorderIterator(groupStart);
         }
      }

      while (iter.hasNext() && !monitor.isCanceled()) {
         ISEDDebugElement next = iter.next();
         
         // Ignore the bo, because either it is ISEDDebugTarget (the very first bo) which has no graphical representation
         // or its a parentnode which already has a graphical representation
         if(next == bo) {
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
               
               if(NodeUtil.canBeGrouped(nextNode)) {
                  GraphicsAlgorithm rectGA = getPictogramElementForBusinessObject(nextNode, 0).getGraphicsAlgorithm();
                  rectGA.setWidth(rectGA.getWidth() + 2 * METOFF);
               }

               if(nextGA.getX() + nextGA.getWidth() > maxX)
                  maxX = nextGA.getX() + nextGA.getWidth();
               
               if(NodeUtil.getGroupStartNode(nextNode) != null) {
//                  System.out.println("NextNode: " + nextNode + ", GN: " + NodeUtil.getGroupStartNode(nextNode));
                  updateAllMethodRectHeights(nextNode);
               }
            }
            if (ArrayUtil.isEmpty(NodeUtil.getChildren(nextNode))) {
               leafs.add(nextNode);
            }
         }
         else if(!ArrayUtil.isEmpty(nextNode.getGroupStartConditions()) && !leafs.contains(nextNode)){
            GraphicsAlgorithm parentGA = getPictogramElementForBusinessObject(NodeUtil.getParent(nextNode)).getGraphicsAlgorithm();
            GraphicsAlgorithm nextGA = nextPE.getGraphicsAlgorithm();
            
//            adjustRects((ISEDDebugNode)bo, monitor);
            
            int mostLeftXAbove = findMostLeftXOfBranchAbove(nextNode);

            // Adjust the remaining BlockEndNodes as if there were just placed under their parents
            moveSubTreeHorizontal(nextNode, mostLeftXAbove - nextGA.getX(), true, monitor);
            nextGA.setX(mostLeftXAbove);
//            moveSubTreeHorizontal(nextNode, parentGA.getX() - nextGA.getX(), true, monitor);

//            if(parentGA.getX() >= nextGA.getX() + METOFF) {
//               moveSubTreeHorizontal(nextNode, parentGA.getX() - nextGA.getX(), true, monitor);
//            }
            
            int mostLeftSub = findMostLeftXInSubtree(nextNode);
            int mostRightXInPrev = findMostRightXInPreviousBranch(nextNode);
            
            // Since the Subtree can now overlap Branches on the Right, adjust them again
            if(mostRightXInPrev != -1 && mostRightXInPrev + OFFSET > mostLeftSub) {
               moveSubTreeHorizontal(nextNode, OFFSET - (mostLeftSub - mostRightXInPrev) , true, monitor);
            }
            
            int biggestWidth = findBiggestWidthInPartTreeAbove(nextNode);
            if(returnBiggerChildOrNull(nextNode, nextGA.getWidth(), monitor) == null && biggestWidth > nextGA.getWidth()) {
               moveSubTreeHorizontal(nextNode, (biggestWidth - nextGA.getWidth()) / 2, true, monitor);
               nextGA.setX(nextGA.getX() - (biggestWidth - nextGA.getWidth()) / 2);
            }

            if(nextGA.getY() < parentGA.getY() + parentGA.getHeight() + OFFSET) {
               moveSubTreeVertical(nextNode, parentGA.getY() + parentGA.getHeight() + OFFSET - nextGA.getY());
               updateAllMethodRectHeights(nextNode);
            }
            
            if(!ArrayUtil.isEmpty(NodeUtil.getChildren(nextNode))) {
               ISEDDebugNode leaf = returnBiggerChildOrNull(nextNode, nextGA.getWidth(), monitor);
               if(leaf != null) {
                  leafs.add(leaf);
                  continue;
               }
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
         if(pe == null) {
            // If auto-collapse is on, we need to create the BC first
            if(parent instanceof ISEDBranchCondition) {
               createGraphicalRepresentationForNode(parent, offsetBetweenPictogramElements, initialX);
               pe = getPictogramElementForBusinessObject(parent);
            }
            else {
               return;
            }
         }
//         System.out.println("Parent: " + parent);
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
            areaX = findMostLeftXOfUpperBranch(node, true);//findMostLeftXOfBranchAbove(node);//findMostLeftXOfBranchInParents(parent);
            if(areaX == -1) {
               areaX = findMostLeftXOfUpperBranch(node, false);
            }
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
            PictogramElement nextPE = getPictogramElementForBusinessObject(next, 0);
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
   protected void centerChildren(final Set<ISEDDebugNode> leafs, 
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
         boolean isGroupStart = NodeUtil.canBeGrouped(next);
         
         ISEDGroupable groupStart = isGroupStart ? (ISEDGroupable) next : null;

         // Go back to root or branch split and collect descendants while computing max width
         // If a parent node has more than one child it is treated as leaf node in a further iteration by adding it to leafs
         List<PictogramElement> descendantsPE = new LinkedList<PictogramElement>();
         int maxWidth = 0;
   //      boolean maxInitialised = false;
         ISEDDebugNode current = next;
         PictogramElement currentPE = nextPE;
         
         
//         System.out.println("centerChildren : current: " + current);
         
         if(isGroupStart && !groupStart.isCollapsed() && NodeUtil.getChildren(current).length < 2) {
            descendantsPE.add(getPictogramElementForBusinessObject(current, 0));
         }
         
         boolean locked = false;
         do {
   //         System.out.println("Current: " + current);
            doneNodes.add(current); // Mark element as centered because it will be done before the next leaf node will be treated in outer most loop
            
            currentPE = getPictogramElementForBusinessObject(current); 
            descendantsPE.add(currentPE);
            
            int currentWidth = currentPE.getGraphicsAlgorithm().getWidth();

            if(next != current && NodeUtil.canBeGrouped(current) && !isParentGroup(next, current)) {
//               System.out.println("centerChildren : C: " + current + ", N: " + next);
               PictogramElement rectPE = getPictogramElementForBusinessObject(current , 0); 
               currentWidth = rectPE.getGraphicsAlgorithm().getWidth();
               descendantsPE.add(rectPE);
            }
//            if(isParentGroup(next, current)) {
//               currentWidth = 
//            }
//            else {
//               PictogramElement rectPE = getPictogramElementForBusinessObject(current , 0); 
//               currentWidth = rectPE.getGraphicsAlgorithm().getWidth();
//               descendantsPE.add(rectPE);
//            }
   
//            int currentWidth = currentPE.getGraphicsAlgorithm().getWidth();
//            int currentWidth = isParentGroup(next, current) ? currentPE.getGraphicsAlgorithm().getWidth() : getPictogramElementForBusinessObject(current , 0).getGraphicsAlgorithm().getWidth();
            if (currentWidth > maxWidth && (!locked || removeChildrenRequired)) {
               maxWidth = currentWidth;
               if(removeChildrenRequired)
                  xStart = currentPE.getGraphicsAlgorithm().getX();
               
//               if(NodeUtil.getChildren(current).length > 1)
//                  locked = true;               
            }
            
            ISEDDebugNode child = current;
            current = NodeUtil.getParent(child);
            
            if(current != null) {
               ISEDDebugNode[] children = NodeUtil.getChildren(current);
               
               if (children.length != 1) {
                  // Update parent only if all of his subbranches are correctly centered
                  if(doneNodes.containsAll(new HashSet<ISEDDebugNode>(Arrays.asList(children)))){
                     leafs.add(current);
                  }
                  current = null;
               }
            }
         } while (current != null && !monitor.isCanceled());
         
         boolean subtreeShiftRequired = false;
         ISEDDebugNode[] children = NodeUtil.getChildren(next, true);
         if (!ArrayUtil.isEmpty(children) && children.length > 1)
         {            
            int subTreeWidth = computeSubTreeWidth(next);
            
            if(maxWidth <= subTreeWidth)
            {
               maxWidth = nextGA.getWidth();
               xMargin = (calculateChildWidth(children) - nextGA.getWidth()) / 2;
               xStart = getPictogramElementForBusinessObject(ArrayUtil.getFirst(children)).getGraphicsAlgorithm().getX();

               // Make sure that the new position is not "lefter" as the old one because this area is reserved for the previous branch and they should not collapse  
               if (xMargin + xStart < nextGA.getX()) {
                  
                  if(!isGroupStart || !groupStart.isCollapsed())
                  {
                     // Collapse possible, so keep old xStart 
                     xMargin = 0;
                     xStart = nextGA.getX();
                     removeChildrenRequired = true;  
                  }
               }
            }
            else {
               subtreeShiftRequired = true;
               xStart = findMostLeftXOfBranchInParents(next);
            }
         }
         
//         System.out.println("XM: " + xMargin + ", XS: " + xStart + ", X: " + nextPE.getGraphicsAlgorithm().getX());
         
   
         // Center collected descendants based on the computed maximal element width
         Iterator<PictogramElement> descendantIter = descendantsPE.iterator();
         while (descendantIter.hasNext() && !monitor.isCanceled()) {
            PictogramElement pe = descendantIter.next();
            GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
            
            int newX = xMargin + xStart + (maxWidth - ga.getWidth()) / 2;

            ga.setX(newX);
            
//            ISEDDebugNode node = (ISEDDebugNode) getBusinessObjectForPictogramElement(pe);
//            if(next != node && !isParentGroup(next, node)) {
//               pe = getPictogramElementForBusinessObject(node, 0);
//               ga = pe.getGraphicsAlgorithm();
//               newX = xMargin + xStart + (maxWidth - ga.getWidth()) / 2;
//               ga.setX(newX);
//            }
//            if(NodeUtil.canBeGrouped(node)) {
//               resizeRectsIfNeeded((ISEDGroupable) node, monitor);
//            }
//            if(node instanceof ISEDStatement) {
//               
//               System.out.println("N: " + node + ", XM: " + xMargin + ", XS: " + xStart + ", XD: " + ((maxWidth - ga.getWidth()) / 2));
//               System.out.println("MW: " + maxWidth + ", gaW: " + ga.getWidth());
//            }
//            System.out.println("N: " + node + ", NEWX: " + (xMargin + xStart + (maxWidth - ga.getWidth()) / 2));
//            System.out.println("N: " + node + ", ??: " + ((maxWidth - ga.getWidth()) / 2));
         }
         
         if(subtreeShiftRequired) {
            PictogramElement firstChildPE = getPictogramElementForBusinessObject(ArrayUtil.getFirst(NodeUtil.getChildren(next)));
            int toMove = nextGA.getX() - firstChildPE.getGraphicsAlgorithm().getX() - (calculateChildWidth(children) - nextGA.getWidth()) / 2;
            moveSubTreeHorizontal(next, toMove, false, monitor);
            
            ISEDGroupable nextGroupStart = NodeUtil.getGroupStartNode(next);
            
            if(nextGroupStart != null) {
               resizeRectsIfNeeded(nextGroupStart, monitor);
            }
         }
         
         
         monitor.worked(1);

         // Center children again if required
         if (removeChildrenRequired && !ArrayUtil.isEmpty(NodeUtil.getChildren(next))) {
            PictogramElement firstChildPE = getPictogramElementForBusinessObject(ArrayUtil.getFirst(NodeUtil.getChildren(next)));
            int offset = nextGA.getX() - firstChildPE.getGraphicsAlgorithm().getX() + (nextGA.getWidth() - calculateChildWidth(children)) / 2;
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
                     
                     if(NodeUtil.canBeGrouped(nextChild)) {
                        nextChildPE = getPictogramElementForBusinessObject(nextChild, 0);
                        if (nextChildPE != null) {
                           nextChildPE.getGraphicsAlgorithm().setX(nextChildPE.getGraphicsAlgorithm().getX() + offset);
                        }
                     }
                  }
               }
            }
         }
      }
      
//      /**
//       * TODO
//       * Hier wird lediglich überprüft, ob der Elternknoten größer als der Subtree ist. Es könnte jedoch sein,
//       * dass ein übergeordneter Knoten zusätzlich größer ist. Muss das beachtet werden? Wenn ja muss man
//       * alle Knoten durchgehen, bis kein größerer mehr exisitert.
//       */
//      
//      if(start != null)
//      {
//         int mostLeftPrevious = findMostLeftXInPreviousBranch(start);
//         int mostLeftFollowing = findMostLeftXInFollowingBranch(start);
//         
//         if(mostLeftFollowing > -1 || mostLeftPrevious > -1)
//         {
//            GraphicsAlgorithm nodeGA = getPictogramElementForBusinessObject(start).getGraphicsAlgorithm();
//            Rectangle newChildrenSubtree = computeSubTreeBounds(start);
//            int biggestWidth = findBiggestWidthInPartTreeAbove(start);
//            
//            // The new Node is bigger than the current Branch
//            if(newChildrenSubtree.width > biggestWidth)
//            {
////               ISEDDebugNode mostLeftNode = findMostLeftXNodeInParentBranches(start);
//               ISEDDebugNode mostLeftNode = findBiggestNodeInParentBranch(start);
//               GraphicsAlgorithm mlnGA = getPictogramElementForBusinessObject(mostLeftNode).getGraphicsAlgorithm();
//               Rectangle subTree = computeSubTreeBounds(mostLeftNode);
//               
//               int diff = (newChildrenSubtree.width - biggestWidth) / 4;
////               System.out.println("MLN: " + mostLeftNode + ", MLX: " + mlnGA.getX() + ", SX: " + subTree.x);
////               System.out.println("MLP: " + mostLeftPrevious + ", MLF: " + mostLeftFollowing);
//               
//               if(mostLeftFollowing > -1 && mlnGA.getX() < subTree.x && (mostLeftPrevious == -1 || mlnGA.getX() > mostLeftPrevious)) {
//                  moveSmallSubtreeFirstBranch(start, mostLeftNode, diff, monitor);
//               }
//               
////               if(mlnGA.getX() < subTree.x && (mostLeftPrevious == -1 || mlnGA.getX() > mostLeftPrevious)) {
////                  int diff = (newChildrenSubtree.width - biggestWidth) / 2;
////                  moveONodes(start, mostLeftNode, -diff, monitor);
////                  System.out.println(diff);
////               }
////               
//               if(mostLeftPrevious > -1 && mlnGA.getX() < subTree.x && mlnGA.getX() < mostLeftPrevious) {
////                  if(mlnGA.getX() + diff > subTree.x) {
////                     diff = (subTree.x - mlnGA.getX()) / 2;
////                  }
////                  
////                  if(mlnGA.getX() + mlnGA.getWidth() < nodeGA.getX() + nodeGA.getWidth()) {
////                     diff /= 2;
////                  }
//      
//                  moveSmallSubTree(start, mostLeftNode, -diff, monitor);
//                  
//                  ISEDGroupable nextGroupStart = NodeUtil.getGroupStartNode(start);
//                  
//                  if(nextGroupStart != null) {
//                     adjustRects((ISEDDebugNode) nextGroupStart, monitor);
//                  }
//               }
//            }
//         }
//      }
   }
   
   protected void adjustSubtreeIfSmaller(ISEDDebugNode node, IProgressMonitor monitor) throws DebugException {
      /**
       * TODO
       * Hier wird lediglich überprüft, ob der Elternknoten größer als der Subtree ist. Es könnte jedoch sein,
       * dass ein übergeordneter Knoten zusätzlich größer ist. Muss das beachtet werden? Wenn ja muss man
       * alle Knoten durchgehen, bis kein größerer mehr exisitert.
       */
      int mostLeftPrevious = findMostLeftXInPreviousBranch(node);
      int mostLeftFollowing = findMostLeftXInFollowingBranch(node);
      
      if(mostLeftFollowing > -1 || mostLeftPrevious > -1)
      {
         Rectangle newChildrenSubtree = computeSubTreeBounds(node);
         int biggestWidth = findBiggestWidthInPartTreeAbove(node);
         
         // The new Node is bigger than the current Branch
         if(newChildrenSubtree.width > biggestWidth)
         {
            ISEDDebugNode mostLeftNode = findBiggestNodeInParentBranch(node);
            GraphicsAlgorithm mlnGA = getPictogramElementForBusinessObject(mostLeftNode).getGraphicsAlgorithm();
            Rectangle subTree = computeSubTreeBounds(mostLeftNode);
            
            int diff = (newChildrenSubtree.width - biggestWidth) / 4;

            if(mostLeftFollowing > -1 && mlnGA.getX() < subTree.x && (mostLeftPrevious == -1 || mlnGA.getX() > mostLeftPrevious)) {
               moveSmallSubtreeFirstBranch(node, mostLeftNode, diff, monitor);
            }
            
//            System.out.println("adjustsmall: mlp: " + mostLeftPrevious + ", ??: " + (mlnGA.getX() < subTree.x) + ", mlnX: " + mlnGA.getX()); 

            // We are at a branch somewhere in the middle or at the end. The free space is not complete taken
            if(mostLeftPrevious > -1 && mlnGA.getX() < subTree.x && mlnGA.getX() < mostLeftPrevious) {  
               moveSmallSubTree(node, mostLeftNode, -diff, monitor);
//               System.out.println("adjustsmall: halle");
            }
            
//            ISEDGroupable nextGroupStart = NodeUtil.getGroupStartNode(node);
//            
//            if(nextGroupStart != null) {
//               adjustRects((ISEDDebugNode) nextGroupStart, monitor);
//            }
         }
      }
   }
   
   protected int calculateChildWidth(ISEDDebugNode[] children) {
      ISEDDebugNode firstChild = ArrayUtil.getFirst(children);
      ISEDDebugNode lastChild = ArrayUtil.getLast(children);
      PictogramElement firstChildPE = getPictogramElementForBusinessObject(firstChild);
      PictogramElement lastChildPE = getPictogramElementForBusinessObject(lastChild);
      return lastChildPE.getGraphicsAlgorithm().getX() + lastChildPE.getGraphicsAlgorithm().getWidth() -
             firstChildPE.getGraphicsAlgorithm().getX();
   }
   
   /**
    * TODO
    * @throws DebugException 
    */
   protected void adjustRects(ISEDDebugNode node, IProgressMonitor monitor) throws DebugException {
      ISEDIterator iter = new SEDPreorderIterator(node);
      while (iter.hasNext() && !monitor.isCanceled()) {
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
      // Either the node or the rect if groupable
      PictogramElement pe = getPictogramElementForBusinessObject(node, 0);
      ISEDGroupable groupStart = NodeUtil.getGroupStartNode(node);
      
      // if the node has no graphical representation or is not in a group, return
      if(pe == null || groupStart == null) {
         return;
      }
      
      GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();

      PictogramElement groupStartPE = getPictogramElementForBusinessObject(groupStart, 0);
      GraphicsAlgorithm groupStartGA = groupStartPE.getGraphicsAlgorithm();
      
      // if the node itself is a group
      if(NodeUtil.canBeGrouped(node))
      {
         // The rects are superimposed, so we need to adjust the nodes/inner rect
         if(ga.getX() == groupStartGA.getX()) {
            int mostLeft = findMostLeftXInGroup(node);
            
            // if there is enough space between the rect and the mostleft inner node, adjust the rect
            if(ga.getX() + METOFF < mostLeft) {
               ga.setX(mostLeft - METOFF);
               resizeRectsIfNeeded((ISEDGroupable) node, monitor);
            }
            // else we have to move the nodes to the right
            else {
               moveRightAndAbove(node, METOFF, monitor);
               moveSubTreeHorizontal(node, METOFF, true, monitor);                  
            }
         }
         
         int mostRightInPrev = findMostRightXInPreviousBranch(node);

         // The rect overlaps a previous branch, so we need to move the nodes to the right
         if(mostRightInPrev > -1)
         {
            if(ga.getX() < mostRightInPrev + OFFSET)
            {
               int toMove = mostRightInPrev + OFFSET - ga.getX();
               moveRightAndAbove(node, toMove, monitor);
               moveSubTreeHorizontal(node, toMove, true, monitor);
            }
            // TODO hier nötig?
            updateAllMethodRectWidths(node);
//               updateAllMethodRectWidths((ISEDGroupable) node, ga, monitor);
         }
      }
      
      // We only need to adjust something if the space between the new node and his group rect is smaller than the offset 
      if(ga.getX() < groupStartGA.getX() + METOFF)
      {
         LinkedList<ISEDGroupable> groups = new LinkedList<ISEDGroupable>();
         ISEDGroupable group = groupStart;
         
         // At first we need to gather all rects we have to adjust
         while(group != null)
         {
            PictogramElement groupPE = getPictogramElementForBusinessObject(group, 0);
            
            //TODO remove
            if(NodeUtil.canBeGrouped(group)) {
            if(groupPE != null) {
               GraphicsAlgorithm groupGA = groupPE.getGraphicsAlgorithm();
               
               // if the new node overlaps the method add it to the grouplist
               if(groupGA.getX() + METOFF > ga.getX()) {
                  groups.addFirst(group);
               }
               else {
                  break;
               }
            }
            }
            
            group = NodeUtil.getGroupStartNode((ISEDDebugNode) group);
         }

         for(int i = 0; i < groups.size(); i++) {
            int metoffAmount = groups.size() - i;
            
            groupStart = groups.get(i);
            ISEDGroupable outerGroup = NodeUtil.getGroupStartNode((ISEDDebugNode) groupStart);

            // if the current group has another outer group we need to check which situation we have
            if(outerGroup != null)
            {
               PictogramElement outerPE = getPictogramElementForBusinessObject(outerGroup, 0);
               GraphicsAlgorithm outerGA = outerPE.getGraphicsAlgorithm();
               groupStartPE = getPictogramElementForBusinessObject(groupStart, 0);
               groupStartGA = groupStartPE.getGraphicsAlgorithm();
//                     System.out.println("Node: " + node);
//                     System.out.println("OX: " + (outerGA.getX() + METOFF) + ", IX: " + mcGA.getX() + ", X: " + ga.getX());
               // TODO nötig?
               if(outerGA.getX() + METOFF <= groupStartGA.getX())
               {
//                     // The new Node overlaps the own Method and the parent Method
//                     if(ga.getX() < outerGA.getX() + METOFF) {
//                        int toMove = outerGA.getX() + METOFF - ga.getX();
//                        moveRightAndAbove(node, toMove, monitor);
//                        moveSubTreeHorizontal(node, toMove, true, monitor);
//                     }
//                     // The new Node just overlaps the own Method
//                     else {
                     // The Node lies in the offset of the parent Method
                  // TODO = fraglich
                     if(ga.getX() - METOFF <= outerGA.getX() + METOFF) {
                        int toMove = outerGA.getX() + METOFF - (ga.getX() - METOFF);
                        moveRightAndAbove(node, toMove, monitor);
                        moveSubTreeHorizontal(node, toMove, true, monitor);
                        groupStartGA.setX(outerGA.getX() + METOFF);
//                        System.out.println("adjust says :o");
                     }
                     else {
                        int mostRightInPrev = findMostRightXInPreviousBranch(node);
                        // The prevbranch is located in the outerMethod and there is at least OFFSET between the prevbranch and the rect
                        if(mostRightInPrev > outerGA.getX() + METOFF && mostRightInPrev + OFFSET <= groupStartGA.getX())
                        {
                           int toMove = groupStartGA.getX() + METOFF - ga.getX();
                           
                           // if the rect is more than OFFSET away move it to the most possible left
                           if(mostRightInPrev + OFFSET < groupStartGA.getX()) {
                              // TODO to validate
                              // Check how much space in relation to methodrects we have
                              int checkRange = metoffAmount;
                              while(mostRightInPrev + OFFSET > groupStartGA.getX() - checkRange * METOFF) {
                                 checkRange--;
                              }
                              
                              groupStartGA.setX(groupStartGA.getX() - toMove - checkRange * METOFF);
//                              System.out.println("adjust says mkay");
                           }
                           // else we have already the minimum space (OFFSET) so move the inner nodes to the right
                           else {
                              moveRightAndAbove(node, toMove, monitor);
                              moveSubTreeHorizontal(node, toMove, true, monitor);
//                              System.out.println("adjust says :D");
                           }
                        }
                        else {//if(outerGA.getX() + METOFF <= ga.getX()) {
//                           System.out.println("adjust says hi");
                           int checkRange = metoffAmount;
                           while(outerGA.getX() + METOFF > ga.getX() - checkRange * METOFF) {
                              checkRange--;
                           }
//                           if(outerGA.getX() + METOFF <= ga.getX() - metoffAmount * METOFF) {
                              groupStartGA.setX(ga.getX() - checkRange * METOFF);
//                           }
//                           else {
//                              System.out.println("adjust say hi");
//                              int toMove = METOFF - ga.getX();
//                              moveRightAndAbove(node, toMove, monitor);
//                              moveSubTreeHorizontal(node, toMove, true, monitor);
//                              groupStartGA.setX(outerGA.getX() + METOFF);
//                           }
                        }
                     }
//                  }
               }
            }
            // else we can just move the nodes to the right
            else {
               int toMove = groupStartGA.getX() + METOFF - ga.getX();
               moveRightAndAbove(node, toMove, monitor);
               moveSubTreeHorizontal(node, toMove, true, monitor);
            }
         }
      }
      
//      ISEDDebugNode mostRightNode = findMostRightNodeInGroup((ISEDDebugNode) groupStart);
//      if(mostRightNode != null) {
////         System.out.println(mostRightNode);
//         updateAllMethodRectWidths(mostRightNode);
////         updateAllMethodRectWidths(groupStart, getPictogramElementForBusinessObject(mostRightNode).getGraphicsAlgorithm(), monitor);
//      }
      
      resizeRectsIfNeeded(groupStart, monitor);
//         if(NodeUtil.canBeGrouped(node))
//         {
//            GraphicsAlgorithm rectGA = getPictogramElementForBusinessObject(node, 0).getGraphicsAlgorithm();
//            
//            // The rects are superimposed, so we need to adjust the nodes/inner rect
//            if(rectGA.getX() == groupStartGA.getX()) {
//               int mostLeft = findMostLeftXInGroup(node);
//               
//               // There is enough space between the rect and the mostleft inner node
//               if(rectGA.getX() + METOFF < mostLeft) {
//                  rectGA.setX(mostLeft - METOFF);
//                  resizeRectsIfNeeded((ISEDGroupable) node, monitor);
//               }
//               // else we have to move the nodes to the right
//               else {
//                  moveRightAndAbove(node, METOFF, monitor);
//                  moveSubTreeHorizontal(node, METOFF, true, monitor);                  
//               }
//            }
//            
//            int mostRightInPrev = findMostRightXInPreviousBranch(node);
//
//            // The rect overlaps a previous branch, so we need to move the nodes to the right
//            if(mostRightInPrev > -1)
//            {
//               if(rectGA.getX() < mostRightInPrev + OFFSET)
//               {
//                  int toMove = mostRightInPrev + OFFSET - rectGA.getX();
//                  moveRightAndAbove(node, toMove, monitor);
//                  moveSubTreeHorizontal(node, toMove, true, monitor);
//               }
//               
//               updateAllMethodRectWidths(node);
////               updateAllMethodRectWidths((ISEDGroupable) node, ga, monitor);
//            }
//            
//            ga = rectGA;
//         }
//         
//         if(ga.getX() < groupStartGA.getX() + METOFF)
//         {
//            ISEDGroupable outerGroup = NodeUtil.getGroupStartNode((ISEDDebugNode) groupStart);
//            if(outerGroup != null)
//            {
//               PictogramElement outerPE = getPictogramElementForBusinessObject(outerGroup, 0);
//               GraphicsAlgorithm outerGA = outerPE.getGraphicsAlgorithm();
////               System.out.println("Node: " + node);
////               System.out.println("OX: " + (outerGA.getX() + METOFF) + ", IX: " + mcGA.getX() + ", X: " + ga.getX());
//               if(outerGA.getX() + METOFF <= groupStartGA.getX())
//               {
//                  // The new Node overlaps the own Method and the parent Method
//                  if(ga.getX() < outerGA.getX() + METOFF) {
//                     int toMove = outerGA.getX() + METOFF - ga.getX();
//                     moveRightAndAbove(node, toMove, monitor);
//                     moveSubTreeHorizontal(node, toMove, true, monitor);
//                  }
//                  // The new Node just overlaps the own Method
//                  else {
//                     // The Node lies in the offset of the parent Method
//                     if(ga.getX() - METOFF <= outerGA.getX() + METOFF) {
//                        int toMove = outerGA.getX() + METOFF - (ga.getX() - METOFF);
//                        moveRightAndAbove(node, toMove, monitor);
//                        moveSubTreeHorizontal(node, toMove, true, monitor);
//                        groupStartGA.setX(outerGA.getX() + METOFF);
//                     }
//                     else {
//                        int mostRightInPrev = findMostRightXInPreviousBranch(node);
//                        
//                        if(mostRightInPrev > outerGA.getX() + METOFF && mostRightInPrev + OFFSET <= groupStartGA.getX())
//                        {
//                           int toMove = groupStartGA.getX() + METOFF - ga.getX();
//                           
//                           if(groupStartGA.getX() - METOFF > mostRightInPrev) {
//                              groupStartGA.setX(groupStartGA.getX() - toMove);
//                           }
//                           else {
//                              moveRightAndAbove(node, toMove, monitor);
//                              moveSubTreeHorizontal(node, toMove, true, monitor);
//                           }
//                        }
//                        else {
//                           if(outerGA.getX() + METOFF /* + OFFSET */ <= ga.getX()) {
//                              if(outerGA.getX() + METOFF <= ga.getX() - METOFF) {
//                                 groupStartGA.setX(ga.getX() - METOFF);
//                              }
//                              else {
//                                 int toMove = METOFF - ga.getX();
//                                 moveRightAndAbove(node, toMove, monitor);
//                                 moveSubTreeHorizontal(node, toMove, true, monitor);
//                                 groupStartGA.setX(outerGA.getX() + METOFF);
//                              }
//                           }
//                        }
//                     }
//                  }
//               }
//            }
//            else { //if(node instanceof ISEDMethodCall || node instanceof ISEDBaseMethodReturn) {
//               int toMove = groupStartGA.getX() + METOFF - ga.getX();
//               moveRightAndAbove(node, toMove, monitor);
//               moveSubTreeHorizontal(node, toMove, true, monitor);
//            }
//            
////            updateParents(pe, METOFF, monitor);
//         }
//         
//         ISEDDebugNode mostRightNode = findMostRightNodeInMethod((ISEDDebugNode) groupStart);
//         if(mostRightNode != null) {
//            updateAllMethodRectWidths(mostRightNode);
////            updateAllMethodRectWidths(groupStart, getPictogramElementForBusinessObject(mostRightNode).getGraphicsAlgorithm(), monitor);
//         }
//         
//         resizeRectsIfNeeded(groupStart, monitor);
//      }
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
//                           System.out.println(node);
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
   protected void updateAllMethodRectHeights(ISEDDebugNode node) throws DebugException {
      GraphicsAlgorithm ga = getPictogramElementForBusinessObject(node).getGraphicsAlgorithm();
      
      ISEDGroupable groupStart = NodeUtil.getGroupStartNode(node);
      boolean isGroupEnd = node.getGroupStartCondition((ISEDDebugNode) groupStart) != null;
      
      int methodMaxY = ga.getY() + ga.getHeight() + (isGroupEnd ? -ga.getHeight() / 2 : OFFSET);

      do
      {
         //TODO remove
         if(NodeUtil.canBeGrouped(groupStart)) {

         GraphicsAlgorithm groupStartGA = getPictogramElementForBusinessObject(groupStart, 0).getGraphicsAlgorithm();
         ISEDBranchCondition[] bcs = groupStart.getGroupEndConditions();
         // Need for inner Method, Fail for outer Method
         for(ISEDBranchCondition bc : bcs) {
            ISEDDebugNode groupEnd = bc.getChildren()[0];
            PictogramElement groupEndPE = getPictogramElementForBusinessObject(groupEnd);
            if(groupEndPE != null) {
               GraphicsAlgorithm groupEndGA = groupEndPE.getGraphicsAlgorithm();
               if(groupEndGA.getY() + groupEndGA.getHeight() / 2 > methodMaxY &&
                     groupEnd.getGroupStartCondition((ISEDDebugNode) NodeUtil.getGroupStartNode((ISEDDebugNode) groupStart)) == null) {
                  methodMaxY = groupEndGA.getY() + groupEndGA.getHeight() / 2;
               }
            }
         }
         
         if(methodMaxY > groupStartGA.getY() + groupStartGA.getHeight())
         {
            groupStartGA.setHeight(methodMaxY - groupStartGA.getY());
            
            // Pushes the nodes down to the end of the Methodrect
            for(ISEDBranchCondition bc : bcs) {
               ISEDDebugNode groupEnd = bc.getChildren()[0];
               
               if(groupEnd == node) {
                  break;
               }
               
               PictogramElement groupEndPE = getPictogramElementForBusinessObject(groupEnd);
               
               if(groupEndPE != null && groupEndPE.getGraphicsAlgorithm().getY() < groupStartGA.getY() + groupStartGA.getHeight()) {
                  int diff = groupStartGA.getY() + groupStartGA.getHeight() - groupEndPE.getGraphicsAlgorithm().getY() -  groupEndPE.getGraphicsAlgorithm().getHeight() / 2;
                  moveSubTreeVertical(groupEnd, diff);
               }
            }
         }
            
         if(isGroupEnd) {
            ga.setY(groupStartGA.getY() + groupStartGA.getHeight() - ga.getHeight() / 2);
//            System.out.println(node);
            
            int deepestY = findDeepestYInGroup(groupStart);
//            System.out.println("GAY: " + ga.getY() + ", DY: " + deepestY);
            if(groupStartGA.getY() + groupStartGA.getHeight() - ga.getHeight() / 2 - deepestY < OFFSET) {
               for(int i = 0; i < bcs.length; i++) {
                  ISEDDebugNode mr = bcs[i].getChildren()[0];
                  PictogramElement mrPE = getPictogramElementForBusinessObject(mr);
                  
                  if(mrPE != null) {
                     moveSubTreeVertical(mr, OFFSET);
                  }
               }
               groupStartGA.setHeight(groupStartGA.getHeight() + OFFSET);
            }
         }
         
         shrinkRectHeights(groupStart);
         
         methodMaxY = groupStartGA.getY() + groupStartGA.getHeight() + ga.getHeight() + OFFSET;// + (isMethodReturn ? - ga.getHeight() / 2 : 0);
         }
         
         groupStart = NodeUtil.getGroupStartNode((ISEDDebugNode) groupStart);
         isGroupEnd = node.getGroupStartCondition((ISEDDebugNode) groupStart) != null;
//         isGroupEnd = false;
//         groupStart = null;
      } while(groupStart != null);
   }
   
   /**
    * TODO
    * @param groupStart
    * @throws DebugException
    */
   protected void shrinkRectHeights(ISEDGroupable groupStart) throws DebugException {
      GraphicsAlgorithm rectGA = null;
      do
      {
         ISEDBranchCondition[] bcs = groupStart.getGroupEndConditions();
         rectGA = getPictogramElementForBusinessObject(groupStart, 0).getGraphicsAlgorithm();
         
         int height = 0;
         for(ISEDBranchCondition bc : bcs) {
            ISEDDebugNode groupEnd = bc.getChildren()[0];
            PictogramElement groupEndPE = getPictogramElementForBusinessObject(groupEnd);
                             
            if(groupEndPE != null && groupEndPE.getGraphicsAlgorithm().getHeight() > height) {
               height = groupEndPE.getGraphicsAlgorithm().getHeight();
            }
         }
         
         int diff = rectGA.getY() + rectGA.getHeight() - findDeepestYInGroup(groupStart) - OFFSET - height / 2;

         if(diff != 0)
         {
            rectGA.setHeight(rectGA.getHeight() - diff);
   
            for(int i = 0; i < bcs.length; i++) {
               ISEDDebugNode groupEnd = bcs[i].getChildren()[0];
               
               // If groupEnd ends another (more outside) group too then ignore it
               if(groupEnd.getGroupStartCondition((ISEDDebugNode) NodeUtil.getGroupStartNode((ISEDDebugNode) groupStart)) != null) {
                  continue;
               }
               
               PictogramElement groupEndPE = getPictogramElementForBusinessObject(groupEnd);
                                
               if(groupEndPE != null) {
                  ISEDGroupable outerGroup = NodeUtil.getGroupStartNode((ISEDDebugNode) groupStart);
                  moveSubTreeBetweenMRVertical(outerGroup, groupEnd, -diff);
               }
            }
         }
         groupStart = NodeUtil.getGroupStartNode((ISEDDebugNode) groupStart);
      } while(groupStart != null);
   }
   
   /**
    * TODO
    * @throws DebugException 
    */
   protected void updateAllMethodRectWidths(ISEDDebugNode node) throws DebugException {
      GraphicsAlgorithm ga = getPictogramElementForBusinessObject(node).getGraphicsAlgorithm();
      
//      ISEDGroupable groupStart = NodeUtil.canBeGrouped(node) ? (ISEDGroupable) node : NodeUtil.getGroupStartNode(node);
      ISEDGroupable groupStart = NodeUtil.getGroupStartNode(node);
      
      int methodMaxX = ga.getX() + ga.getWidth() + METOFF;
      while(groupStart != null)
      {
         GraphicsAlgorithm groupStartGA = getPictogramElementForBusinessObject(groupStart, 0).getGraphicsAlgorithm();

         //TODO remove
         if(NodeUtil.canBeGrouped(groupStart)) {
         if(methodMaxX > groupStartGA.getX() + groupStartGA.getWidth()) {
            int diff = methodMaxX - groupStartGA.getX() - groupStartGA.getWidth();
            groupStartGA.setWidth(groupStartGA.getWidth() + diff);
         }
         }
         
         methodMaxX = groupStartGA.getX() + groupStartGA.getWidth() + METOFF;
         groupStart = NodeUtil.getGroupStartNode((ISEDDebugNode) groupStart);
      }
   }

//   /**
//    * TODO
//    * @throws DebugException 
//    */
//   protected void updateAllMethodRectWidths(ISEDGroupable groupStart, GraphicsAlgorithm peGA, IProgressMonitor monitor) throws DebugException {
//      int methodMaxX = peGA.getX() + peGA.getWidth() + METOFF;
//      GraphicsAlgorithm groupStartGA;
//      do
//      {
//         groupStartGA = getPictogramElementForBusinessObject(groupStart, 0).getGraphicsAlgorithm();
//
//         if(methodMaxX > groupStartGA.getX() + groupStartGA.getWidth()) {
//            int diff = methodMaxX - groupStartGA.getX() - groupStartGA.getWidth();
//            groupStartGA.setWidth(groupStartGA.getWidth() + diff);
//         }
//         
//         methodMaxX = groupStartGA.getX() + groupStartGA.getWidth() + METOFF;
//         groupStart = NodeUtil.getGroupStartNode((ISEDDebugNode) groupStart);
//      } while(groupStart != null && !monitor.isCanceled());
//   }
   
   protected void resizeRectsIfNeeded(ISEDGroupable groupStart, IProgressMonitor monitor) throws DebugException {
      do
      {
         PictogramElement groupStartPE = getPictogramElementForBusinessObject(groupStart, 0);

         // TODO remove
         if(NodeUtil.canBeGrouped(groupStart)) {
         if(groupStartPE != null)
         {
            GraphicsAlgorithm rectGA = groupStartPE.getGraphicsAlgorithm();
            
            int mostLeftX = findMostLeftXInGroup((ISEDDebugNode) groupStart) - METOFF;

            if(mostLeftX > rectGA.getX() && NodeUtil.getGroupStartNode((ISEDDebugNode) groupStart) != null) {
               rectGA.setX(mostLeftX);
            }

            rectGA.setWidth(findMostRightXInGroup(groupStart, (ISEDDebugNode) groupStart) + METOFF - rectGA.getX());
         }
         }
         groupStart = NodeUtil.getGroupStartNode((ISEDDebugNode) groupStart);
      } while(groupStart != null);
   }
   
   /**
    * TODO
    * @param start
    * @return
    * @throws DebugException
    */
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
    * TODO
    * @param start
    * @return
    * @throws DebugException
    */
   protected ISEDDebugNode findBiggestNodeInParentBranch(ISEDDebugNode start) throws DebugException {
      ISEDDebugNode node = start;
      ISEDDebugNode biggestNode = null;

      while(node != null) {
         node = NodeUtil.getParent(node);
         
         if(NodeUtil.getChildren(node).length > 1) {
            break;
         }
      }
      
      int width = -1;
      while(node != null) {
//      while(node != null && (NodeUtil.getChildren(node).length == 1 || width == -1)) {
         PictogramElement nodePE = getPictogramElementForBusinessObject(node);
         if(nodePE != null)
         {
            GraphicsAlgorithm nodeGA = nodePE.getGraphicsAlgorithm();
            if(nodeGA.getWidth() > width || width == -1) {
               width = nodeGA.getWidth();
               biggestNode = node;
            }
         }
         
         node = NodeUtil.getParent(node);
      }

      return biggestNode;
   }

   /**
    * Searches the sibling node which is X coordinate is more to the right
    * and which is the one which is most left of all siblings.
    * @param node The {@link ISEDDebugNode} to search in.
    * @return The found {@link PictogramElement} or {@code null} if no one was found.
    * @throws DebugException Occurred Exception.
    */
//   protected PictogramElement findMostLeftSiblingPE(ISEDDebugNode node) throws DebugException {
//      PictogramElement sibling = null;
//      if (node != null) {
//         ISEDDebugNode parent = NodeUtil.getParent(node);
//         while (parent != null && sibling == null) {
//            ISEDDebugNode[] siblings = NodeUtil.getChildren(parent);
//            int index = ArrayUtil.indexOf(siblings, node);
//            if (index < 0) {
//               throw new DebugException(LogUtil.getLogger().createErrorStatus("Child \"" + node + "\" is not contained in parent's children \"" + Arrays.toString(siblings) + "\"."));
//            }
//            if (index < siblings.length - 1) {
//               sibling = findMostLeftNodePE(siblings[index + 1]);
//            }
//            else {
//               node = parent;
//               parent = NodeUtil.getParent(node);
//            }
//         }
//      }
//      return sibling;
//   }
   
   /**
    * Searches the node in the subtree starting at the given {@link ISEDDebugNode}
    * which has the X coordinate most left.
    * @param node The {@link ISEDDebugNode} to search in.
    * @return The found {@link PictogramElement} of the most left node or {@code null} if no one was found.
    * @throws DebugException Occurred Exception.
    */
//   protected PictogramElement findMostLeftNodePE(ISEDDebugNode node) throws DebugException {
//      // Compute initial left position
//      ISEDDebugNode mostLeft = node;
//      PictogramElement mostLeftPE = getPictogramElementForBusinessObject(mostLeft);
//      // Iterate over most left sub trees
//      while (node != null) {
//         // Check if the current node is more left
//         PictogramElement nodePE = getPictogramElementForBusinessObject(node);
//         if (nodePE != null && nodePE.getGraphicsAlgorithm().getX() < mostLeftPE.getGraphicsAlgorithm().getX()) {
//            mostLeft = node;
//            mostLeftPE = nodePE;
//         }
//         // Change node for next loop iteration
//         ISEDDebugNode[] children = NodeUtil.getChildren(node);
//         if (!ArrayUtil.isEmpty(children)) {
//            node = children[0];
//         }
//         else {
//            node = null;
//         }
//      }
//      return mostLeftPE;
//   }
   
   /**
    * Iterates over the parents of the given {@link ISEDDebugNode} until
    * the beginning of the branch is reached if only the current Branch should
    * be searched or until we finish a Branch which isn't the first one.
    * Meanwhile it computes the x value of the most left visited {@link ISEDDebugNode}.
    * @param node
    * @param onlyCurrentBranch Determines if only the current Branch will be processed or the parent branches too
    * @return mostLeftXInBranch The most left x-Coordinate
    * @throws DebugException
    */
   protected int findMostLeftXOfUpperBranch(ISEDDebugNode node, boolean onlyCurrentBranch) throws DebugException {
      int mostLeftXInBranch = -1;
      ISEDDebugNode parent = node;
      
      while (parent != null) {
         PictogramElement pe = getPictogramElementForBusinessObject(parent, (isParentGroup(node, parent) ? 1 : 0));
         
         if (pe != null) {            
            if (pe.getGraphicsAlgorithm().getX() < mostLeftXInBranch || mostLeftXInBranch == -1) {
               mostLeftXInBranch = pe.getGraphicsAlgorithm().getX();
            }
         }
         
         // Select parent for next loop iteration
         ISEDDebugNode child = parent;
         parent = NodeUtil.getParent(parent);
         if (parent != null && NodeUtil.getChildren(parent).length != 1) {
            if(onlyCurrentBranch) {
               parent = null;
            }
            onlyCurrentBranch = true;
         }
      }
      return mostLeftXInBranch;
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
      int mostLeftXInBranch = -1;
      ISEDDebugNode parent = node;
      
      while (parent != null) {
         PictogramElement pe = getPictogramElementForBusinessObject(parent, (isParentGroup(node, parent) ? 1 : 0));
         
         if (pe != null) {            
            if (pe.getGraphicsAlgorithm().getX() < mostLeftXInBranch || mostLeftXInBranch == -1) {
               mostLeftXInBranch = pe.getGraphicsAlgorithm().getX();
//                  System.out.println("Node: " + node + ", X: " + mostLeftXInBranch);
            }
         }
         
         // Select parent for next loop iteration
//         ISEDDebugNode child = node;
         parent = NodeUtil.getParent(parent);
         if (parent != null && NodeUtil.getChildren(parent).length != 1) {
//         if (node != null && NodeUtil.getChildren(node).length != 1 && !ArrayUtil.isFirst(NodeUtil.getChildren(node), child)) {
            parent = null;
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
            return findMostLeftXInSubtree(ArrayUtil.getPrevious(children, node));
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
//   protected ISEDDebugNode findMostLeftXNodeInParentBranches(ISEDDebugNode node) throws DebugException {
////      int mostLeftXInBranch = -1;
//      ISEDDebugNode mostLeftNode = null;
//      while (node != null) {
//         PictogramElement pe = getPictogramElementForBusinessObject(node);
//         if (pe != null) {
////            System.out.println(node);
////            System.out.println("NX: " + pe.getGraphicsAlgorithm().getWidth() + ", OX: " + (mostLeftNode == null ? 0 : getPictogramElementForBusinessObject(mostLeftNode).getGraphicsAlgorithm().getWidth()));
////            if (mostLeftNode == null || pe.getGraphicsAlgorithm().getWidth() > getPictogramElementForBusinessObject(mostLeftNode).getGraphicsAlgorithm().getWidth()) {
//            if (mostLeftNode == null || pe.getGraphicsAlgorithm().getX() < getPictogramElementForBusinessObject(mostLeftNode).getGraphicsAlgorithm().getX()) {
//               mostLeftNode = node;
//            }
//         }        
//         
//         // Select parent for next loop iteration
//         ISEDDebugNode child = node;
//         node = NodeUtil.getParent(node);
////         if (node != null && NodeUtil.getChildren(node).length != 1 && ArrayUtil.isFirst(NodeUtil.getChildren(node), child)) {
////            node = null;
////         }
//      }
//      return mostLeftNode;
////      GraphicsAlgorithm ga = null;
////      while (node != null) {
////         PictogramElement pe = getPictogramElementForBusinessObject(node);
////         if (pe != null) {
////            if (pe.getGraphicsAlgorithm().getX() < mostLeftXInBranch || mostLeftXInBranch == -1) {
////               mostLeftXInBranch = pe.getGraphicsAlgorithm().getX();
////            }
////         }        
////         
////         // Select parent for next loop iteration
////         ISEDDebugNode child = node;
////         node = NodeUtil.getParent(node);
////         if (node != null && NodeUtil.getChildren(node).length != 1 && !ArrayUtil.isLast(NodeUtil.getChildren(node), child)) {
////            node = null;
////         }
////      }
////      return mostLeftXInBranch;
////      int mostLeftXInBranch = -1;
////      do
////      {
////         ISEDDebugNode parent = NodeUtil.getParent(node);
////         
////         if(parent == null) {
////            return mostLeftXInBranch;
////         }
////
////         if(NodeUtil.getChildren(parent).length != 1) {
////            while (parent != null) {
////               PictogramElement pe = getPictogramElementForBusinessObject(parent);
////               if (pe != null) {
////                  if (pe.getGraphicsAlgorithm().getX() < mostLeftXInBranch || mostLeftXInBranch == -1) {
////                     mostLeftXInBranch = pe.getGraphicsAlgorithm().getX();
////                  }
////               }
////               
////               // Select parent for next loop iteration
////               parent = NodeUtil.getParent(parent);
////               if (parent != null && NodeUtil.getChildren(parent).length != 1) {
////                  parent = null;
////               }
////            }
////            return mostLeftXInBranch;
////         }
////         
////         node = parent;
////      } while(true);
//   }
   
   /**
    * Iterates over the most left children of the given {@link ISEDDebugNode}
    * and computes the minimal x value of the visited child {@link ISEDDebugNode}s.
    * @param node The {@link ISEDDebugNode} to start.
    * @return The most minimal x value of most left child {@link ISEDDebugNode}s.
    * @throws DebugException Occurred Exception.
    */
   protected int findMostLeftXInSubtree(ISEDDebugNode node) throws DebugException {
      int mostLeftXInSubtree = -1;
      while (node != null) {
         PictogramElement pe = getPictogramElementForBusinessObject(node, 0);
         if (pe != null) {
            if (pe.getGraphicsAlgorithm().getX() < mostLeftXInSubtree || mostLeftXInSubtree == -1) {
               mostLeftXInSubtree = pe.getGraphicsAlgorithm().getX();
            }
         }
         // Select child for next loop iteration
         node = ArrayUtil.getFirst(NodeUtil.getChildren(node));
      }
      return mostLeftXInSubtree;
   }
   
   protected int findMostLeftXInGroup(ISEDDebugNode node) throws DebugException {
      int mostLeftXInSubtree = -1;
      ISEDGroupable groupStart = NodeUtil.canBeGrouped(node) ? (ISEDGroupable) node : NodeUtil.getGroupStartNode(node);
      while (node != null) {
//         if(!node.equals(mc)) {
//         System.out.println("Node: " + node + ", MC: " + mc + ", E?: " + (node instanceof ISEDMethodCall && !node.equals(mc)));
            PictogramElement pe = (NodeUtil.canBeGrouped(node) && (ISEDGroupable) node != groupStart) ? getPictogramElementForBusinessObject(node, 0) : getPictogramElementForBusinessObject(node);
            if (pe != null) {
               GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
               if (ga.getX() < mostLeftXInSubtree || mostLeftXInSubtree == -1) {
                  mostLeftXInSubtree = ga.getX();
               }
            }
//         }
         // Select child for next loop iteration
         ISEDDebugNode parent = node;
         node = ArrayUtil.getFirst(NodeUtil.getChildren(node));
//         System.out.println("Node: " + parent + ", Child: " + node);
//         if(node != null && ArrayUtil.isEmpty(node.getCallStack()) && !(node instanceof ISEDBranchCondition)
//               || parent instanceof ISEDMethodReturn && parent.getCallStack()[0].equals(mc)) {
         if(node != null && NodeUtil.getGroupStartNode(node) == null
               || !ArrayUtil.isEmpty(parent.getGroupStartConditions()) && NodeUtil.getGroupStartNode(parent) == groupStart) {
            node = null;
         }
      }
      return mostLeftXInSubtree;
   }
   
   /**
    * TODO
    * @param node
    * @return
    * @throws DebugException
    */
   protected ISEDDebugNode findMostRightNodeInGroup(ISEDDebugNode node) throws DebugException {
      int mostRightXInSubtree = -1;
      ISEDDebugNode mostRightNode = null;
      ISEDDebugNode groupStart = node;
      while (node != null) {
         if(!node.equals(groupStart)) {
            PictogramElement pe = (node instanceof ISEDGroupable && !node.equals(groupStart)) ? getPictogramElementForBusinessObject(node, 0) : getPictogramElementForBusinessObject(node);
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
         if(node != null && NodeUtil.getGroupStartNode(node) == null
               || !ArrayUtil.isEmpty(parent.getGroupStartConditions()) && NodeUtil.getGroupStartNode(parent) == groupStart) {
            node = null;
         }
//         if(node != null && ArrayUtil.isEmpty(node.getCallStack()) && !(node instanceof ISEDBranchCondition)
//               || parent instanceof ISEDMethodReturn && parent.getCallStack()[0].equals(mc)) {
//            node = null;
//         }
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
         PictogramElement pe = getPictogramElementForBusinessObject(node, 0);
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
         PictogramElement pe = getPictogramElementForBusinessObject(node, 0);
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
   
   /**
    * Iterates over the most right children in the Method of the given {@link ISEDDebugNode}
    * and computes the maximal x value (x + width) of the visited child {@link ISEDDebugNode}s.
    * @param node The {@link ISEDDebugNode} to start.
    * @return The most maximal x value of most right child {@link ISEDDebugNode}s.
    * @throws DebugException Occurred Exception.
    */
   protected int findMostRightXInGroup(ISEDGroupable groupStart, ISEDDebugNode node) throws DebugException {
      int mostRightXInSubtree = 0;
      ISEDDebugNode start = node;
      while (node != null) {
         PictogramElement pe = NodeUtil.canBeGrouped(node) && !node.equals(start) ? getPictogramElementForBusinessObject(node, 0) : getPictogramElementForBusinessObject(node);
         if (pe != null) {
            GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
            if (ga.getX() + ga.getWidth() > mostRightXInSubtree) {
               mostRightXInSubtree = ga.getX() + ga.getWidth();
            }
         }
         // Select child for next loop iteration
         ISEDDebugNode parent = node;
         node = ArrayUtil.getLast(NodeUtil.getChildren(node, true));
         if(node != null && NodeUtil.getGroupStartNode(node) == null
               || !ArrayUtil.isEmpty(parent.getGroupStartConditions()) && NodeUtil.getGroupStartNode(parent) == groupStart) {
            node = null;
         }
//         if(node != null && ArrayUtil.isEmpty(node.getCallStack()) && !(node instanceof ISEDBranchCondition) ||
//               parent instanceof ISEDBaseMethodReturn && parent.getCallStack()[0].equals(groupStart)) {
//            node = null;
//         }
      }
      return mostRightXInSubtree;
   }
   
   /**
    * TODO
    * @param groupStart
    * @return
    * @throws DebugException
    */
   protected int findDeepestYInGroup(ISEDGroupable groupStart) throws DebugException {
      int deepestY = 0;
      int groupAmount = -1;
      ISEDIterator iter = new SEDGroupPreorderIterator(groupStart);

      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();
         
         if(next instanceof ISEDDebugNode)
         {
            ISEDDebugNode nextNode = (ISEDDebugNode) next;
            // Either we are outside of the Group or we have reached a groupendnode
            if(NodeUtil.getGroupStartNode(nextNode) == null) {
               continue;
            }
            else if(nextNode.getGroupStartCondition((ISEDDebugNode) groupStart) != null) {
               boolean endNodeReached = false;
               for(ISEDBranchCondition bc : nextNode.getGroupStartConditions()) {
                  if(NodeUtil.getParent(bc) == groupStart) {
                     endNodeReached = true;     
                  }
               }
               
               if(endNodeReached) {
                  continue;
               }
            }
//            if(nodeGroupStart == null || nextNode.getGroupStartCondition((ISEDDebugNode) groupStart) != null && nodeGroupStart == groupStart) {
//               continue;
//            }
            
            PictogramElement pe = getPictogramElementForBusinessObject(nextNode);
            if (pe != null) {
               GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
               if (ga.getY() + ga.getHeight() > deepestY) {
                  deepestY = ga.getY() + ga.getHeight();
//                  System.out.println("DYN: " + nextNode + ", DY: " + deepestY);

                  if(!ArrayUtil.isEmpty(nextNode.getGroupStartConditions())) {
                     nextNode = NodeUtil.getParent(nextNode.getInnerMostVisibleGroupStartCondition());
//                     nextNode = (ISEDDebugNode) nodeGroupStart;
                  }
                  
                  ISEDGroupable innerGroup = NodeUtil.getGroupStartNode(nextNode);
                  
                  groupAmount = -1;
                  // We need to compute the amount of Groups inside the startgroup
                  while(innerGroup != null && innerGroup != groupStart) {
//                     System.out.println("IG: " + innerGroup);
                     groupAmount++;
                     innerGroup = NodeUtil.getGroupStartNode((ISEDDebugNode) innerGroup);
                  }
                  
//                  if(!ArrayUtil.isEmpty(nextNode.getCallStack())) {
//                     int index = ArrayUtil.indexOf(nextNode.getCallStack(), groupStart);
//
//                     if(index != -1) {
//                        groupAmount = index; 
//                     }
//                  }
               }
            }
         }
      }
      
      return groupAmount > 0 ? deepestY + groupAmount * OFFSET : deepestY;
//      return deepestY + groupAmount * OFFSET;
   }
   
   /**
    * TODO
    * @throws DebugException 
    */
   protected boolean isParentGroup(ISEDDebugNode source, ISEDDebugNode potentialGroupNode) throws DebugException {
      if(NodeUtil.canBeGrouped(potentialGroupNode)) {
         ISEDGroupable outerGroup = NodeUtil.getGroupStartNode(source);
         
         while(outerGroup != null) {
            if(outerGroup == (ISEDGroupable) potentialGroupNode) {
               return true;
            }
            outerGroup = NodeUtil.getGroupStartNode((ISEDDebugNode) outerGroup);
         }
      }
      
      return false;
   }
//   protected boolean hasInnerMethod(ISEDGroupable groupStart) throws DebugException {
//      ISEDIterator iter = new SEDGroupPreorderIterator(groupStart);
//      while (iter.hasNext()) {
//         ISEDDebugElement next = iter.next();
//         
//         if(next instanceof ISEDGroupable && !next.equals(groupStart)) {
//            return true;
//         }
//      }
//      
//      return false;
//   }
   
   /*
    * TODO
    */
   protected ISEDDebugNode returnBiggerChildOrNull(ISEDDebugNode node, int width, IProgressMonitor monitor) throws DebugException {
      ISEDIterator iter = new SEDPreorderIterator(node);
      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();
         
         if(next instanceof ISEDDebugNode) {
            ISEDDebugNode nextNode = (ISEDDebugNode) next;
            PictogramElement nextPE = getPictogramElementForBusinessObject(nextNode);
            if(nextPE != null) {
               GraphicsAlgorithm nextGA = nextPE.getGraphicsAlgorithm();
//               System.out.println("N: " + node + ", W: " + width + ", NW: " + nextGA.getWidth());
               if(nextGA.getWidth() > width) {
                  return nextNode;
               }
            }
         }
      }
      
      return null;
   }
   
   /**
    * TODO
    * @param node
    * @param width
    * @return
    * @throws DebugException
    */
//   protected boolean hasBiggerChild(ISEDDebugNode node, int width) throws DebugException {
//      ISEDIterator iter = new SEDPreorderIterator(node);
//      while (iter.hasNext()) {
//         ISEDDebugElement next = iter.next();
//         
//         if(next instanceof ISEDDebugNode) {
//            ISEDDebugNode nextNode = (ISEDDebugNode) next;
//            PictogramElement nextPE = getPictogramElementForBusinessObject(nextNode);
//            if(nextPE != null) {
//               GraphicsAlgorithm nextGA = nextPE.getGraphicsAlgorithm();
//               if(nextGA.getWidth() > width) {
//                  return true;
//               }
//            }
//         }
//      }
//      
//      return false;
//   }
   
   /**
    * Moves all nodes in the sub tree between the given {@link ISEDMethodReturn} and
    * the next {@link ISEDMethodReturn} or {@link ISEDTermination} vertical by the given distance.
    * @param mr The {@link ISEDDebugNode} to start with.
    * @param node The {@link ISEDDebugNode} to start moving.
    * @param distance The distance to move in y direction.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception
    */
   protected void moveSubTreeBetweenMRVertical(ISEDGroupable groupStart, ISEDDebugNode node, int distance) throws DebugException {
      
      ISEDIterator iter = groupStart == null ? new SEDPreorderIterator(node) : new SEDGroupPreorderIterator(groupStart, node);
      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();            
         
         if(next instanceof ISEDDebugNode) {
            ISEDDebugNode nextNode = (ISEDDebugNode) next;
            
            if(nextNode.getGroupStartCondition((ISEDDebugNode) groupStart) != null && !nextNode.equals(node)) {
               continue;
            }
//            if(!ArrayUtil.isEmpty(nextNode.getGroupStartConditions()) && !nextNode.equals(node)) {
//               continue;
//            }
//            if(next == null || next instanceof ISEDBaseMethodReturn && !next.equals(node)) {
//               continue;
//            }
            
            
            PictogramElement pe = getPictogramElementForBusinessObject(nextNode);
            if (pe != null) {
               GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
               ga.setY(ga.getY() + distance);
            }
            
            if(NodeUtil.canBeGrouped(nextNode)) {
               pe = getPictogramElementForBusinessObject(nextNode, 0);
               if (pe != null) {
                  GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
                  ga.setY(ga.getY() + distance);
               }
            }
         }
      }
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
               moveSubTreeHorizontal(siblings[i], distance, true, monitor);
            }
            // Re-center parent
         int childWidth = calculateChildWidth(siblings);
         PictogramElement firstChildPE = getPictogramElementForBusinessObject(ArrayUtil.getFirst(siblings));

            PictogramElement parentPE = getPictogramElementForBusinessObject(parent);
            GraphicsAlgorithm parentGA = parentPE.getGraphicsAlgorithm();

            int xMargin = (childWidth - parentGA.getWidth()) / 2;
            int xStart = firstChildPE.getGraphicsAlgorithm().getX();
            
            parentGA.setX(xStart + xMargin);

            if(NodeUtil.getGroupStartNode(parent) != null) {
               updateAllMethodRectWidths(parent);
//               updateAllMethodRectWidths(NodeUtil.getGroupStartNode(parent), parentGA, monitor);
            }
            // Define node for next loop iteration
            node = parent;
            parent = NodeUtil.getParent(node);
         }
      }
   }
   
   /**
    * Moves all nodes which x coordinate is more to the left as the 
    * given node by the given distance. If called by {@code adjustSubtreeIfSmaller}
    * the distance is negative!
    * @param node The {@link ISEDDebugNode} to start moving.
    * @param distance The distance to move.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   protected void moveSmallSubTree(ISEDDebugNode node, ISEDDebugNode endNode, int distance, IProgressMonitor monitor) throws DebugException {
      if (node != null) {
         ISEDDebugNode parent = NodeUtil.getParent(node);
         
         ISEDGroupable groupStart = NodeUtil.getGroupStartNode(node);
         
         if(groupStart != null) {
            GraphicsAlgorithm rectGA = getPictogramElementForBusinessObject(groupStart, 0).getGraphicsAlgorithm();
            rectGA.setX(rectGA.getX() + distance);
         }
         
         boolean firstBranch = true;
         
         // Move the subtrees under the big node in the right directions
         while (parent != null && parent != endNode && !monitor.isCanceled()) {
//            System.out.println("Parent: " + parent + ", End: " + endNode + ", ?: " + (parent != endNode));
            ISEDDebugNode[] siblings = NodeUtil.getChildren(parent);
            int index = ArrayUtil.indexOf(siblings, node);
            if (index < 0) {
               throw new DebugException(LogUtil.getLogger().createErrorStatus("Child \"" + node + "\" is not contained in parent's children \"" + Arrays.toString(siblings) + "\"."));
            }
            
            // TODO
            if(siblings.length > 1)
            {
               // This is the startbranch (called the method). It needs to compute normally
               if(firstBranch) {
                  moveSubTreeHorizontal(siblings[index], distance, true, monitor);
                  firstBranch = false;
               }
               // All other Branches on the right side need to be moved to the right
               else {
                  moveSubTreeHorizontal(siblings[index], -distance, true, monitor);
               }
               // Move subtree of all siblings
               for (int i = index - 1; i > -1; i--) {
                  moveSubTreeHorizontal(siblings[i], distance, true, monitor);
               }
               
               // This distance is halfed each time we go one branch up
               distance /= 2;
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
   protected void moveSmallSubtreeFirstBranch(ISEDDebugNode node, ISEDDebugNode endNode, int distance, IProgressMonitor monitor) throws DebugException {
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
               /**
                * Distance is -3/4 for the currentBranch and 1/4 for following siblings
                * Problem: Result is not integer so Tests may fail
                */
               if(firstBranch) {
//                  GraphicsAlgorithm ga = getPictogramElementForBusinessObject(parent, 0).getGraphicsAlgorithm();
//                  ga.setX(ga.getX() - 3 * distance);
                  moveSubTreeHorizontal(siblings[index], -3 * distance, true, monitor);
                  System.out.println("mSSFB: sib: " + siblings[index]);
                  firstBranch = false;
               }
               // All other Branches on the left side need to be moved to the left
               else {
                  moveSubTreeHorizontal(siblings[index], -distance, true, monitor);
               }
//               // Move subtree of all siblings
               for (int i = index + 1; i < siblings.length; i++) {
                  System.out.println("mSSFB: sib: " + siblings[i]);
                  moveSubTreeHorizontal(siblings[i], distance, true, monitor);
               }
               
               // This distance is halfed each time we go one branch up
               distance /= 2;
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
                              boolean moveRoot,
                              IProgressMonitor monitor) throws DebugException {
      ISEDIterator iter = new SEDPreorderIterator(root);
      while (iter.hasNext()) {
         ISEDDebugElement node = iter.next();
         
         if(node == root && !moveRoot) {
            continue;
         }
         
         PictogramElement pe = getPictogramElementForBusinessObject(node);
         if (pe != null) {
            GraphicsAlgorithm peGA = pe.getGraphicsAlgorithm();
            peGA.setX(peGA.getX() + distance);
            ISEDDebugNode dn = (ISEDDebugNode) node;

            if(NodeUtil.canBeGrouped(dn))
            {
               pe = getPictogramElementForBusinessObject(node, 0);
               if (pe != null) {
                  peGA = pe.getGraphicsAlgorithm();
                  peGA.setX(peGA.getX() + distance);
               }
            }
            
            if(NodeUtil.getGroupStartNode(dn) != null) {
               updateAllMethodRectWidths(dn);
//               GraphicsAlgorithm mcGA = getPictogramElementForBusinessObject(dn.getCallStack()[0], 0).getGraphicsAlgorithm();
//               System.out.println("Node: " + dn + ", MX:" + (peGA.getX() + peGA.getWidth() + METOFF) + ", X: " + (mcGA.getX() + METOFF));
//               updateAllMethodRectWidths(NodeUtil.getGroupStartNode(dn), peGA, monitor);
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
         
         if(NodeUtil.canBeGrouped((ISEDDebugNode) next)) {
            pe = getPictogramElementForBusinessObject(next, 0);
            if (pe != null) {
               GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
               ga.setY(ga.getY() + distance);
            }
         }
      }
   }
   
   /**
    * TODO
    * @param start
    * @param distance
    * @param monitor
    * @throws DebugException
    */
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

         if(NodeUtil.canBeGrouped(parent)) {
               ISEDGroupable outerGroup = NodeUtil.getGroupStartNode(start);
               boolean isParentGroup = false;
               
               while(outerGroup != null) {
                  if(outerGroup == (ISEDGroupable) parent) {
                     isParentGroup = true;
                     break;
                  }
                  outerGroup = NodeUtil.getGroupStartNode((ISEDDebugNode) outerGroup);
               }
               
               if(!isParentGroup) {
                  parentPE = getPictogramElementForBusinessObject(parent, 0);
                  parentGA = parentPE.getGraphicsAlgorithm();
                  parentGA.setX(parentGA.getX() + distance);
               }
            
//          if(NodeUtil.canBeGrouped(parent) && outerGroup != null && outerGroup != (ISEDGroupable) parent) {
//             parentPE = getPictogramElementForBusinessObject(parent, 0);
//             parentGA = parentPE.getGraphicsAlgorithm();
//             parentGA.setX(parentGA.getX() + distance);
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