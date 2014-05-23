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
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.util.ISEDIterator;
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
            // Update children, they have the correct layout after this step
            final int OFFSET = getDiagram().getGridUnit() * 2;
            if (success) {
               success = updateChildren(pictogramElement, OFFSET, new SubProgressMonitor(monitor, 1));
            }
            monitor.worked(1);
            // Update parents, because children maybe have now a bigger width and overlap with other branches
            if (success) {
               success = updateParents(pictogramElement, OFFSET, new SubProgressMonitor(monitor, 1));
            }
            monitor.worked(1);
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
                  centerChildren(leafs, monitor);
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
      PictogramElement parentPE = null;
      while (iter.hasNext() && !monitor.isCanceled()) {
         ISEDDebugElement next = iter.next();
         PictogramElement nextPE = getPictogramElementForBusinessObject(next);
         if (nextPE == null) {
            if (next instanceof ISEDDebugNode) { // Ignore ISEDDebugTarget which has no graphical representation
               ISEDDebugNode nextNode = (ISEDDebugNode)next;
               createGraphicalRepresentationForNode(parentPE, nextNode, offsetBetweenPictogramElements, initialX);
               nextPE = getPictogramElementForBusinessObject(next);
               if (nextPE != null) {
                  // Update maxX to make sure that ISEDDebugTargets don't overlap each other.
                  GraphicsAlgorithm nextGA = nextPE.getGraphicsAlgorithm();
                  if (nextGA.getX() + nextGA.getWidth() > maxX) {
                     maxX = nextGA.getX() + nextGA.getWidth();
                  }
               }
               if (ArrayUtil.isEmpty(nextNode.getChildren())) {
                  leafs.add(nextNode);
               }
            }
         }
         parentPE = nextPE;
         monitor.worked(1);
      }
      return leafs;
   }
   
   /**
    * Creates a new graphical representation for the given {@link ISEDDebugNode}.
    * @param parentPE The {@link PictogramElement} of {@link ISEDDebugNode#getParent()} or {@code null} if it is an {@link ISEDThread}.
    * @param node The {@link ISEDDebugNode} for that a graphical representation is needed.
    * @param offsetBetweenPictogramElements The offset between {@link PictogramElement}s, e.g. to parent or to previous sibling.
    * @param initialX The initial X value which is used if no parentPE is defined.
    * @throws DebugException Occurred Exception.
    */
   protected void createGraphicalRepresentationForNode(PictogramElement parentPE,
                                                       ISEDDebugNode node,
                                                       int offsetBetweenPictogramElements,
                                                       int initialX) throws DebugException { 
      AreaContext areaContext = new AreaContext();
      if (parentPE != null) {
         ISEDDebugNode parent = node.getParent();
         if (parent != null) {
            ISEDDebugNode previousSibling = ArrayUtil.getPrevious(parent.getChildren(), node);
            if (previousSibling != null) {
               // Compute bounds of the sub tree starting by the previous sibling.
               Rectangle previousBounds = computeSubTreeBounds(previousSibling);
               if (previousBounds != null) {
                  // Add right to the previous sibling directly under parent
                  areaContext.setX(previousBounds.width() + offsetBetweenPictogramElements); 
                  areaContext.setY(previousBounds.y());
               }
               else {
                  // Add directly under parent
                  // Add directly under parent, but use x of most left pe in branch
                  int x = findMostLeftXOfBranchInParents(parent);
                  GraphicsAlgorithm parentGA = parentPE.getGraphicsAlgorithm();
                  areaContext.setX(x); 
                  areaContext.setY(parentGA.getY() + parentGA.getHeight() + offsetBetweenPictogramElements);
               }
            }
            else {
               // Add directly under parent, but use x of most left pe in branch
               int x = findMostLeftXOfBranchInParents(parent);
               GraphicsAlgorithm parentGA = parentPE.getGraphicsAlgorithm();
               areaContext.setX(x); 
               areaContext.setY(parentGA.getY() + parentGA.getHeight() + offsetBetweenPictogramElements);
            }
         }
         else {
            // Add directly under parent
            GraphicsAlgorithm parentGA = parentPE.getGraphicsAlgorithm();
            areaContext.setX(parentGA.getX()); 
            areaContext.setY(parentGA.getY() + parentGA.getHeight() + offsetBetweenPictogramElements);
         }
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
    * Iterates over the parents of the given {@link ISEDDebugNode} until
    * the beginning of the branch is reached and computes the x value
    * of the most left visited {@link ISEDDebugNode}.
    * @param node The {@link ISEDDebugNode} to start.
    * @return The most left x value of parent {@link ISEDDebugNode}s in the same branch.
    * @throws DebugException Occurred Exception.
    */
   protected int findMostLeftXOfBranchInParents(ISEDDebugNode node) throws DebugException {
      int mostLeftXInBranch = 0;
      boolean mostLeftXInBranchInitialized = false;
      while (node != null) {
         PictogramElement pe = getPictogramElementForBusinessObject(node);
         if (pe != null) {
            if (mostLeftXInBranchInitialized) {
               if (pe.getGraphicsAlgorithm().getX() < mostLeftXInBranch) {
                  mostLeftXInBranch = pe.getGraphicsAlgorithm().getX();
               }
            }
            else {
               mostLeftXInBranch = pe.getGraphicsAlgorithm().getX();
               mostLeftXInBranchInitialized = true;
            }
         }
         // Select parent for next loop iteration
         node = node.getParent();
         if (node != null && node.getChildren().length != 1) {
            node = null;
         }
      }
      return mostLeftXInBranch;
   }

   /**
    * Computes the bounds of the sub tree starting at the given {@link ISEDDebugNode}.
    * @param root The sub tree.
    * @return The bounds of the subtree where {@link Rectangle#x()}, {@link Rectangle#y()} is the minimal point and {@link Rectangle#width()}, {@link Rectangle#height()} the maximal point. The result is {@code null} if the subtree is {@code null} or has no graphical representations.
    * @throws DebugException Occurred Exception.
    */
   protected Rectangle computeSubTreeBounds(ISEDDebugNode root) throws DebugException {
      Rectangle result = null;
      if (root != null) {
         ISEDIterator iter = new SEDPreorderIterator(root);
         while (iter.hasNext()) {
            ISEDDebugElement next = iter.next();
            PictogramElement nextPE = getPictogramElementForBusinessObject(next);
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
               ISEDDebugNode[] children = element.getChildren();
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
         // Compute new x margin to center current branch under his children 
         int xMargin;
         int xStart;
         boolean removeChildrenRequired = false;
         if (!ArrayUtil.isEmpty(next.getChildren())) {
            ISEDDebugNode firstChild = ArrayUtil.getFirst(next.getChildren());
            ISEDDebugNode lastChild = ArrayUtil.getLast(next.getChildren());
            PictogramElement firstChildPE = getPictogramElementForBusinessObject(firstChild);
            PictogramElement lastChildPE = getPictogramElementForBusinessObject(lastChild);
            int childWidth = lastChildPE.getGraphicsAlgorithm().getX() + lastChildPE.getGraphicsAlgorithm().getWidth() - 
                             firstChildPE.getGraphicsAlgorithm().getX(); 
            xMargin = (childWidth - nextPE.getGraphicsAlgorithm().getWidth()) / 2;
            xStart = firstChildPE.getGraphicsAlgorithm().getX();
            // Make sure that the new position is not "lefter" as the old one because this area is reserved for the previous branch and they should not collapse  
            if (xMargin + xStart < nextPE.getGraphicsAlgorithm().getX()) {
               // Collapse possible, so keep old xStart 
               xMargin = 0;
               xStart = nextPE.getGraphicsAlgorithm().getX();
               removeChildrenRequired = true;
            }
         }
         else {
            xMargin = 0;
            xStart = nextPE.getGraphicsAlgorithm().getX();
         }
         
         // Go back to root or branch split and collect descendants while computing max width
         // If a parent node has more than one child it is treated as leaf node in a further iteration by adding it to leafs
         List<PictogramElement> descendantsPE = new LinkedList<PictogramElement>();
         int maxWidth = 0;
         boolean maxInitialised = false;
         ISEDDebugNode current = next;
         PictogramElement currentPE = nextPE;
         do {
            doneNodes.add(current); // Mark element as centered because it will be done before the next leaf node will be treated in outer most loop 
            currentPE = getPictogramElementForBusinessObject(current);
            descendantsPE.add(currentPE);
            int currentWidth = currentPE.getGraphicsAlgorithm().getWidth();
            if (maxInitialised) {
               if (currentWidth > maxWidth) {
                  maxWidth = currentWidth;
               }
            }
            else {
               maxWidth = currentWidth;
               maxInitialised = true;
            }
            ISEDDebugNode child = current;
            current = child.getParent();
            if (current != null && current.getChildren().length != 1) {
               if (ArrayUtil.isLast(current.getChildren(), child)) {  // Update parent only if all of his branches are correctly centered
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
            ga.setX(xMargin + xStart + (maxWidth - ga.getWidth()) / 2);
         }
         monitor.worked(1);
         // Center children again if required
         if (removeChildrenRequired && !ArrayUtil.isEmpty(next.getChildren())) {
            ISEDDebugNode lastChild = ArrayUtil.getLast(next.getChildren());
            int mostRightX = findMostRightXInSubtree(lastChild);
            int offset = (maxWidth - (mostRightX - xStart)) / 2;
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
                  ISEDDebugNode parent = node.getParent();
                  if (parent != null) {
                     // Find most left node in righter nodes
                     PictogramElement mostLeftSiblingPE = findMostLeftSiblingPE(node);
                     if (mostLeftSiblingPE != null) {
                        // Compute maximal branch x and width
                        int maxXOnParents = findMostRightXOfBranchInParents(node);
                        int maxXInChildren = findMostRightXInSubtree(node);
                        int maxXOfBranch = maxXOnParents > maxXInChildren ? maxXOnParents : maxXInChildren; 
                        // Compute distance to move righter nodes
                        int distance = maxXOfBranch + offsetBetweenPictogramElements - mostLeftSiblingPE.getGraphicsAlgorithm().getX();
                        if (distance != 0) {
                           // Move righter nodes by the given distance
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
    * Searches the sibling node which is X coordinate is more to the right
    * and which is the one which is most left of all siblings.
    * @param node The {@link ISEDDebugNode} to search in.
    * @return The found {@link PictogramElement} or {@code null} if no one was found.
    * @throws DebugException Occurred Exception.
    */
   protected PictogramElement findMostLeftSiblingPE(ISEDDebugNode node) throws DebugException {
      PictogramElement sibling = null;
      if (node != null) {
         ISEDDebugNode parent = node.getParent();
         while (parent != null && sibling == null) {
            ISEDDebugNode[] siblings = parent.getChildren();
            int index = ArrayUtil.indexOf(siblings, node);
            if (index < 0) {
               throw new DebugException(LogUtil.getLogger().createErrorStatus("Child \"" + node + "\" is not contained in parent's children \"" + Arrays.toString(siblings) + "\"."));
            }
            if (index < siblings.length - 1) {
               sibling = findMostLeftNodePE(siblings[index + 1]);
            }
            else {
               node = parent;
               parent = node.getParent();
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
         ISEDDebugNode[] children = node.getChildren();
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
         PictogramElement pe = getPictogramElementForBusinessObject(node);
         if (pe != null) {
            if (mostRightXInBranchInitialized) {
               if (pe.getGraphicsAlgorithm().getX() + pe.getGraphicsAlgorithm().getWidth() > mostRightXInBranch) {
                  mostRightXInBranch = pe.getGraphicsAlgorithm().getX() + pe.getGraphicsAlgorithm().getWidth();
               }
            }
            else {
               mostRightXInBranch = pe.getGraphicsAlgorithm().getX() + pe.getGraphicsAlgorithm().getWidth();
               mostRightXInBranchInitialized = true;
            }
         }
         // Select parent for next loop iteration
         node = node.getParent();
         if (node != null && node.getChildren().length != 1) {
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
         PictogramElement pe = getPictogramElementForBusinessObject(node);
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
         ISEDDebugNode[] children = node.getChildren();
         node = ArrayUtil.getLast(children);
      }
      return mostRightXInSubtree;
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
         ISEDDebugNode parent = node.getParent();
         while (parent != null && !monitor.isCanceled()) {
            ISEDDebugNode[] siblings = parent.getChildren();
            int index = ArrayUtil.indexOf(siblings, node);
            if (index < 0) {
               throw new DebugException(LogUtil.getLogger().createErrorStatus("Child \"" + node + "\" is not contained in parent's children \"" + Arrays.toString(siblings) + "\"."));
            }
            // Move subtree of all siblings
            for (int i = index + 1; i < siblings.length; i++) {
               moveSubTree(siblings[i], distance, monitor);
            }
            // Re-center parent
            ISEDDebugNode firstChild = ArrayUtil.getFirst(siblings);
            ISEDDebugNode lastChild = ArrayUtil.getLast(siblings);
            PictogramElement parentPE = getPictogramElementForBusinessObject(parent);
            PictogramElement firstChildPE = getPictogramElementForBusinessObject(firstChild);
            PictogramElement lastChildPE = getPictogramElementForBusinessObject(lastChild);
            int childWidth = lastChildPE.getGraphicsAlgorithm().getX() + lastChildPE.getGraphicsAlgorithm().getWidth() - 
                             firstChildPE.getGraphicsAlgorithm().getX();
            int xMargin = (childWidth - parentPE.getGraphicsAlgorithm().getWidth()) / 2;
            int xStart = firstChildPE.getGraphicsAlgorithm().getX();
            parentPE.getGraphicsAlgorithm().setX(xStart + xMargin);
            // Define node for next loop iteration
            node = parent;
            parent = node.getParent();
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
   protected void moveSubTree(ISEDDebugNode root, 
                              int distance, 
                              IProgressMonitor monitor) throws DebugException {
      ISEDIterator iter = new SEDPreorderIterator(root);
      while (iter.hasNext() && !monitor.isCanceled()) {
         ISEDDebugElement node = iter.next();
         PictogramElement pe = getPictogramElementForBusinessObject(node);
         if (pe != null) {
            pe.getGraphicsAlgorithm().setX(pe.getGraphicsAlgorithm().getX() + distance);
         }
      }
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