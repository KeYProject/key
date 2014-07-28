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
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.IReason;
import org.eclipse.graphiti.features.IUpdateFeature;
import org.eclipse.graphiti.features.context.IUpdateContext;
import org.eclipse.graphiti.features.impl.Reason;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.algorithms.Rectangle;
import org.eclipse.graphiti.mm.algorithms.RoundedRectangle;
import org.eclipse.graphiti.mm.algorithms.Text;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.mm.pictograms.Shape;
import org.eclipse.graphiti.services.Graphiti;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.util.ISEDIterator;
import org.key_project.sed.core.util.SEDPreorderIterator;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeStyleUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilterWithException;

/**
 * Implementation of {@link IUpdateFeature} for {@link ISEDMethodCall}s.
 * @author Martin Hentschel
 */
public class MethodCallUpdateFeature extends AbstractDebugNodeUpdateFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IUpdateFeature}.
    */   
   public MethodCallUpdateFeature(IFeatureProvider fp) {
      super(fp);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IReason updateNeeded(IUpdateContext context) {
      PictogramElement pe = context.getPictogramElement();
      ISEDMethodCall mc = (ISEDMethodCall) getBusinessObjectForPictogramElement(pe);

      if(!(pe.getGraphicsAlgorithm() instanceof Rectangle) && !mc.isCollapsed())
         return super.updateNeeded(context);
      
      return Reason.createFalseReason();
   }

// @Override
// public boolean update(IUpdateContext context) {
////    super.update(context);
//    System.out.println("MU: " + context.getPictogramElement());
////    System.out.println("C");
//    return false;
// }

//   /**
//    * {@inheritDoc}
//    */
//   @Override
//   public boolean update(IUpdateContext context) {
//      Object updateStyle = context.getProperty(KEY_UPDATE_STYLE);
//      if (updateStyle instanceof Boolean && ((Boolean)updateStyle).booleanValue()) {
//         Object nodeProp = context.getProperty(KEY_SED_NODE);
//         ISEDDebugNode bo = nodeProp instanceof ISEDDebugNode ? (ISEDDebugNode)nodeProp : null;
//         if (bo == null) {
//            bo = (ISEDDebugNode)getFeatureProvider().getBusinessObjectForPictogramElement(context.getPictogramElement());
//         }
//         return updateStyle(context.getPictogramElement(), bo);
//      }
//      else {
//         try {
//            // Define monitor to use
//            IProgressMonitor monitor = GraphitiUtil.getProgressMonitor(context);
//            // Update name
//            PictogramElement pictogramElement = context.getPictogramElement();
//            monitor.beginTask("Update element: " + pictogramElement, 3);
//            boolean success = updateName(pictogramElement, new SubProgressMonitor(monitor, 1));
//            monitor.worked(1);
//            // Update children, they have the correct layout after this step
//            final int OFFSET = getDiagram().getGridUnit() * 2;
//            if (success) {
//               success = updateChildren(pictogramElement, OFFSET, new SubProgressMonitor(monitor, 1));
//            }
//            monitor.worked(1);
//            // Update parents, because children maybe have now a bigger width and overlap with other branches
//            if (success) {
//               success = updateParents(pictogramElement, OFFSET, new SubProgressMonitor(monitor, 1));
//            }
//            monitor.worked(1);
//            monitor.done();
//            return success;
//         }
//         catch (DebugException e) {
//            LogUtil.getLogger().logError(e);
//            return false;
//         }
//      }
//   }
   
   protected int computeSubTreeWidth(ISEDDebugNode root) throws DebugException {
      int result = -1;
      if (root != null) {
         ISEDIterator iter = new SEDPreorderIterator(root);
         while (iter.hasNext()) {
            ISEDDebugElement next = iter.next();
            PictogramElement nextPE = getPictogramElementForBusinessObject(next);
            if (nextPE != null) {
               GraphicsAlgorithm nextGA = nextPE.getGraphicsAlgorithm();
               if (result == -1) {
                  result = nextGA.getX() + nextGA.getWidth();
               }
               else if (nextGA.getX() + nextGA.getWidth() > result) {
                  result = nextGA.getX() + nextGA.getWidth();
               }
            }
         }
      }
      return result;
   }

//      /**
//       * Computes the bounds of the sub tree starting at the given {@link ISEDDebugNode}.
//       * @param root The sub tree.
//       * @return The bounds of the subtree where {@link Rectangle#x()}, {@link Rectangle#y()} is the minimal point and {@link Rectangle#width()}, {@link Rectangle#height()} the maximal point. The result is {@code null} if the subtree is {@code null} or has no graphical representations.
//       * @throws DebugException Occurred Exception.
//       */
//      protected Rectangle computeSubTreeBounds(ISEDDebugNode root) throws DebugException {
//         Rectangle result = null;
//         if (root != null) {
//            ISEDIterator iter = new SEDPreorderIterator(root);
//            while (iter.hasNext()) {
//               ISEDDebugElement next = iter.next();
//               PictogramElement nextPE = getPictogramElementForBusinessObject(next);
//               if (nextPE != null) {
//                  GraphicsAlgorithm nextGA = nextPE.getGraphicsAlgorithm();
//                  if (result == null) {
//                     result = new Rectangle(nextGA.getX(), 
//                                            nextGA.getY(), 
//                                            nextGA.getX() + nextGA.getWidth(), 
//                                            nextGA.getY() + nextGA.getHeight());
//                  }
//                  else {
//                     if (nextGA.getX() < result.x()) {
//                        result.setX(nextGA.getX());
//                     }
//                     if (nextGA.getY() < result.y()) {
//                        result.setY(nextGA.getY());
//                     }
//                     if (nextGA.getX() + nextGA.getWidth() > result.width()) {
//                        result.setWidth(nextGA.getX() + nextGA.getWidth());
//                     }
//                     if (nextGA.getY() + nextGA.getHeight() > result.height()) {
//                        result.setHeight(nextGA.getY() + nextGA.getHeight());
//                     }
//                  }
//               }
//            }
//         }
//         return result;
//      }
   
   /**
    * Centers all nodes starting from the given leaf nodes.
    * @param leafs All leaf nodes.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception
    */
   protected void centerCollapsedMethod(ISEDBranchCondition[] bcs) throws DebugException {
      final Set<ISEDDebugNode> doneNodes = new HashSet<ISEDDebugNode>(); // Contains all already centered nodes
      final Set<ISEDDebugNode> leafs = new HashSet<ISEDDebugNode>();
      
      for(ISEDBranchCondition bc : bcs) {
         leafs.add(bc.getChildren()[0]);
      }
      
      while (!leafs.isEmpty()) {
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
         
         final PictogramElement nextPE = next instanceof ISEDMethodCall ? getMethodCallPE(next, 1) : getPictogramElementForBusinessObject(next);
         
//            System.out.println("N:" + next + ", NPE: " + nextPE.getGraphicsAlgorithm());
         // Compute new x margin to center current branch under his children 
         int xMargin;
         int xStart;
         boolean removeChildrenRequired = false;
            if (next instanceof ISEDMethodCall) {
               ISEDDebugNode firstChild = ArrayUtil.getFirst(bcs);
               ISEDDebugNode lastChild = ArrayUtil.getLast(bcs);
               PictogramElement firstChildPE = getPictogramElementForBusinessObject(firstChild);
               PictogramElement lastChildPE = getPictogramElementForBusinessObject(lastChild);
               int childWidth = lastChildPE.getGraphicsAlgorithm().getX() + lastChildPE.getGraphicsAlgorithm().getWidth() - 
                                firstChildPE.getGraphicsAlgorithm().getX(); 
               xMargin = (childWidth - nextPE.getGraphicsAlgorithm().getWidth()) / 2;
               xStart = firstChildPE.getGraphicsAlgorithm().getX();
            }
            else {
            xMargin = 0;
            xStart = nextPE.getGraphicsAlgorithm().getX();
//               
//               System.out.println("nPE: " + nextPE.getGraphicsAlgorithm() + ", nextPEX: " + nextPE.getGraphicsAlgorithm().getX());
            }
//            System.out.println("nPE: " + nextPE.getGraphicsAlgorithm() + ", nextPEX: " + nextPE.getGraphicsAlgorithm().getX());
//            System.out.println("XM: " + xMargin + ", XS: " + xStart);
         
         // Go back to root or branch split and collect descendants while computing max width
         // If a parent node has more than one child it is treated as leaf node in a further iteration by adding it to leafs
         List<PictogramElement> descendantsPE = new LinkedList<PictogramElement>();
         int maxWidth = -1;
         ISEDDebugNode current = next;
         PictogramElement currentPE = nextPE;
         do {
            doneNodes.add(current); // Mark element as centered because it will be done before the next leaf node will be treated in outer most loop
            currentPE = current instanceof ISEDMethodCall ?
                  getFeatureProvider().getAllPictogramElementsForBusinessObject(current)[1] : 
                  getPictogramElementForBusinessObject(current);

            descendantsPE.add(currentPE);

            int currentWidth = currentPE.getGraphicsAlgorithm().getWidth();
            if (currentWidth > maxWidth) {
               maxWidth = currentWidth;
            }
            
            ISEDDebugNode child = current;
            
            if(child instanceof ISEDMethodReturn) {
               ISEDMethodReturn mr = (ISEDMethodReturn) child;
               current = mr.getMethodReturnCondition();
            }
            else if(child instanceof ISEDBranchCondition){
               ISEDBranchCondition bc = (ISEDBranchCondition) child;
//               current = bc.getChildren()[0].getCallStack()[0];
               if (ArrayUtil.isLast(bcs, bc)) {  // Update parent only if all of his branches are correctly centered
                  leafs.add(bc.getChildren()[0].getCallStack()[0]);
               }
               current = null;
            }
            else {
               current = child.getParent();
               if (current != null && current.getChildren().length != 1) {
                  if (ArrayUtil.isLast(bcs, child)) {  // Update parent only if all of his branches are correctly centered
                     leafs.add(current);
                  }
                  current = null;
               }
            }
//
//            if (current != null && current.getChildren().length != 1) {
//               if (ArrayUtil.isLast(bcs, child)) {  // Update parent only if all of his branches are correctly centered
//                  leafs.add(current);
//               }
//               current = null;
//            }
         } while (current != null);
         // Center collected descendants based on the computed maximal element width
         Iterator<PictogramElement> descendantIter = descendantsPE.iterator();
         while (descendantIter.hasNext()) {
            PictogramElement pe = descendantIter.next();
            GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
            ga.setX(xMargin + xStart + (maxWidth - ga.getWidth()) / 2);
//            System.out.println("XM: " + xMargin + ", XS: " + xStart + ", R: " + (maxWidth - ga.getWidth()) / 2);
         }

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
                           PictogramElement pe = getPictogramElementForBusinessObject(node);
                           // Move righter nodes by the given distance
                           moveRighterNodes(node, distance, monitor);
                           
                           if(node.getCallStack().length > 0)
                           {
                              ISEDDebugNode currentNode = node;
                              PictogramElement currentPE = getPictogramElementForBusinessObject(currentNode);
                              GraphicsAlgorithm currentGA = currentPE.getGraphicsAlgorithm();
                              
                              ISEDDebugNode mcNode = node.getCallStack()[0];
                              
                              do
                              {
                                 pe = getFeatureProvider().getAllPictogramElementsForBusinessObject(mcNode)[0];
                                 int methodWidth = Integer.parseInt(Graphiti.getPeService().getPropertyValue(pe, "width"));

                                 if(currentNode instanceof ISEDMethodCall) {
                                    currentGA = pe.getGraphicsAlgorithm();
                                 }

                                 if(currentGA.getWidth() + distance > methodWidth ||
                                       mcNode.getCallStack().length == 0)
                                 {
                                    Graphiti.getPeService().setPropertyValue(pe, "width", Integer.toString(methodWidth + distance));
                                    pe.getGraphicsAlgorithm().setWidth(methodWidth + distance);
//                                       updateMethodWidth(pe, methodWidth + distance);
                                 }
                                 
                                 mcNode = mcNode.getCallStack().length > 0 ? mcNode.getCallStack()[0] : null;

                              } while(mcNode != null);
                           }
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
   protected void updateMethod(PictogramElement pe, GraphicsAlgorithm ga) throws DebugException {
      int methodWidth = Integer.parseInt(Graphiti.getPeService().getPropertyValue(pe, "width"));
      int methodHeight = Integer.parseInt(Graphiti.getPeService().getPropertyValue(pe, "height"));
      int methodOffX = Integer.parseInt(Graphiti.getPeService().getPropertyValue(pe, "offX"));
      int methodOffY = Integer.parseInt(Graphiti.getPeService().getPropertyValue(pe, "offY"));

      int methodMaxX = ga.getX() - methodOffX + ga.getWidth();
//         System.out.println("WHX? X: " + ga.getX() + ", W: " + ga.getWidth());
//         System.out.println("MW: " + methodWidth + ", MX: " + methodMaxX);
      if(methodMaxX > methodWidth)
      {
         Graphiti.getPeService().setPropertyValue(pe, "width", Integer.toString(methodMaxX));
//            updateMethodWidth(pe, methodMaxX);
         pe.getGraphicsAlgorithm().setWidth(methodMaxX);
      }

      int methodMaxY = ga.getY() - methodOffY + ga.getHeight();
//         System.out.println("WHY? Y: " + ga.getY() + ", H: " + ga.getHeight());
      if(methodMaxY > methodHeight)
      {
         Graphiti.getPeService().setPropertyValue(pe, "height", Integer.toString(methodMaxY - 10));
         pe.getGraphicsAlgorithm().setHeight(methodMaxY - 10);
         GraphicsAlgorithm peGA = pe.getGraphicsAlgorithm();
         
         ISEDMethodCall mc = (ISEDMethodCall) getBusinessObjectForPictogramElement(pe);
         ISEDBranchCondition[] conds = mc.getMethodReturnConditions();
         
         for(int i = 0; i < conds.length; i++) {
            ISEDDebugNode node = conds[i].getChildren()[0];
            PictogramElement nodePE = getPictogramElementForBusinessObject(node);
            
            if(nodePE != null) {
               GraphicsAlgorithm nodeGA = nodePE.getGraphicsAlgorithm();
               moveSubTreeVertical(node, peGA.getY() + peGA.getHeight() - nodeGA.getY() - 10);
//                  nodeGA.setY(peGA.getY() + peGA.getHeight() - 10);
            }
         }
         
//            for(ISEDDebugNode node : exceptions) {
//               PictogramElement nodePE = getPictogramElementForBusinessObject(node);
//               System.out.println(":)");
//               if(nodePE != null) {
//                  GraphicsAlgorithm nodeGA = nodePE.getGraphicsAlgorithm();
//                  nodeGA.setY(peGA.getY() + peGA.getHeight() - 10);
//                  System.out.println("Halklk");
////                  moveSubTreeVertical(node, peGA.getY() + peGA.getHeight() - nodeGA.getY() - 10);
//               }
//            }
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
            int newX = 0;
//               if(parent instanceof ISEDMethodCall) {
//                  newX -= Integer.parseInt(Graphiti.getPeService().getPropertyValue(parentPE, "offX"));
//                  parentPE = ((ContainerShape) parentPE).getChildren().get(1);
//               }

            int xMargin = (childWidth - parentPE.getGraphicsAlgorithm().getWidth()) / 2;
            int xStart = firstChildPE.getGraphicsAlgorithm().getX();
            newX += xStart + xMargin;
            
            parentPE.getGraphicsAlgorithm().setX(newX);
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
   protected void moveSubTreeHorizontal(ISEDDebugNode root, 
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
    * {@inheritDoc}
    */
   @Override
   protected boolean canUpdateBusinessObject(Object businessObject) {
      return businessObject instanceof ISEDMethodCall;
   }
}