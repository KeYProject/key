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


import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.IReason;
import org.eclipse.graphiti.features.IUpdateFeature;
import org.eclipse.graphiti.features.context.IUpdateContext;
import org.eclipse.graphiti.features.context.impl.AddContext;
import org.eclipse.graphiti.features.context.impl.AreaContext;
import org.eclipse.graphiti.features.context.impl.RemoveContext;
import org.eclipse.graphiti.features.context.impl.UpdateContext;
import org.eclipse.graphiti.features.impl.DefaultRemoveFeature;
import org.eclipse.graphiti.features.impl.Reason;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.algorithms.Polyline;
import org.eclipse.graphiti.mm.algorithms.Rectangle;
import org.eclipse.graphiti.mm.pictograms.AnchorContainer;
import org.eclipse.graphiti.mm.pictograms.Connection;
import org.eclipse.graphiti.mm.pictograms.ConnectionDecorator;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.eclipse.graphiti.services.IPeCreateService;
import org.eclipse.graphiti.util.ColorConstant;
import org.key_project.sed.core.model.ISEDBaseMethodReturn;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDExceptionalTermination;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.core.util.ISEDIterator;
import org.key_project.sed.core.util.NodeUtil;
import org.key_project.sed.core.util.SEDMethodPreorderIterator;
import org.key_project.sed.core.util.SEDPreorderIterator;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeStyleUtil;
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
   
   /*
    * TODO
    */
   protected void updateCollapse(ISEDMethodCall mc, IProgressMonitor monitor) throws DebugException {
      GraphicsAlgorithm rectGA = getPictogramElementForBusinessObject(mc, 0).getGraphicsAlgorithm();
      GraphicsAlgorithm nodeGA = getPictogramElementForBusinessObject(mc).getGraphicsAlgorithm();
      
      ISEDBranchCondition[] bcs = NodeUtil.getSortedBCs(mc);

      removeChildren(mc, mc);
      removeConnections(getPictogramElementForBusinessObject(mc));
      
      mc.setCollapsed(true);

      int maxX = rectGA.getX();
      Set<ISEDDebugNode> leafs = new HashSet<ISEDDebugNode>();

      if(bcs.length > 1) {
         int above = findBiggestWidthInPartTreeAbove(mc);
         if(above > rectGA.getWidth()) {
//            leafs.add(mc);
            nodeGA.setX(nodeGA.getX() - (above - nodeGA.getWidth()) / 2);
         }
         else
            nodeGA.setX(maxX);
//         leafs.add(mc);
//         nodeGA.setX(findMostLeftXInMethod(node));
      }
      else {
//         moveRightAndAbove(mc, maxX - nodeGA.getX(), monitor);
         nodeGA.setX(rectGA.getX());
      }
      
      boolean recenterMR = false;
      for(ISEDBranchCondition bc : bcs)
      {
         createGraphicalRepresentationForNode(bc, OFFSET, maxX);
         
         PictogramElement bcPE = getFeatureProvider().getPictogramElementForBusinessObject(bc);
         GraphicsAlgorithm bcGA = bcPE.getGraphicsAlgorithm();

         ISEDBaseMethodReturn mr = (ISEDBaseMethodReturn) bc.getChildren()[0];
         PictogramElement mrPE = getFeatureProvider().getPictogramElementForBusinessObject(mr);
         GraphicsAlgorithm mrGA = mrPE.getGraphicsAlgorithm();
         
         if(maxX == rectGA.getX() && bcGA.getX() < maxX + METOFF) {
            bcGA.setX(maxX + METOFF);
         }
         
         if(bcs.length == 1) {
            int newX = findMostLeftXOfBranchInParents(mc);
            if(findBiggestWidthInPartTreeAbove(mr) < mrGA.getWidth()) {
               newX += METOFF;
            }
            
            mrGA.setX(newX);
         }

         if(bcGA.getWidth() < mrGA.getWidth() && bcs.length == 1) {
            bcGA.setX(mrGA.getX() + (mrGA.getWidth() - bcGA.getWidth()) / 2);
//            mrGA.setX(mrGA.getX() - METOFF);
         }
         else {
            if(!hasBiggerChild(mr, mrGA.getWidth()) || recenterMR) {
               int hMove = bcGA.getX() - mrGA.getX() + (bcGA.getWidth() - mrGA.getWidth()) / 2;
   //            System.out.println(hMove);
               moveSubTreeHorizontal(mr, hMove, new SubProgressMonitor(monitor, 1));
               
               int mostLeft = findMostLeftXInSubtree(bc);
               if(mostLeft < bcGA.getX()) {
                  moveSubTreeHorizontal(bc, bcGA.getX() - mostLeft, new SubProgressMonitor(monitor, 1));
   //               System.out.println(bc);
               }
               
               recenterMR = true;
            }
//            leafs.add((bcGA.getWidth() > mrGA.getWidth() ? bc : mr));
         }
         
         maxX = findMostRightXInSubtree(bc) + OFFSET;

         createConnection((AnchorContainer)bcPE, (AnchorContainer)mrPE);
         
         leafs.add((bcGA.getWidth() > mrGA.getWidth() ? bc : mr));
         
//         if(bcs.length == 1)
//         {
////            System.out.println(findMostLeftXOfBranchInParents(NodeUtil.getParent(mc)) + " -> " + mrGA.getX());
////            if(findMostLeftXOfBranchInParents(NodeUtil.getParent(mc)) > mrGA.getX()) {
////               mrGA.setX(mrGA.getX() - METOFF);
////            }
////            if(findBiggestWidthInPartTreeAbove(mr) > mrGA.getWidth()) {
////               mrGA.setX(mrGA.getX() - METOFF);
////            }
////            if(findBiggestWidthInPartTreeAbove(mr) < mrGA.getWidth()) {
////               nodeGA.setX(rectGA.getX() + METOFF);
//               leafs.add((bcGA.getWidth() > mrGA.getWidth() ? bc : mr));
////            }
//         }
      }

      shrinkRectHeights(mc);
      centerChildren(mc, new HashSet<ISEDDebugNode>(leafs), new SubProgressMonitor(monitor, 1));
      monitor.worked(1);
      
//      resizeRectsIfNeeded(mc, monitor);
      
      if(bcs.length == 1)
      {
         for(ISEDDebugNode leaf : leafs) {
            
            if(ArrayUtil.isEmpty(NodeUtil.getChildren(leaf))) {
               continue;
            }
            
            PictogramElement leafPE = getFeatureProvider().getPictogramElementForBusinessObject(leaf);
            GraphicsAlgorithm leafGA = leafPE.getGraphicsAlgorithm();
            
            ISEDDebugNode child = NodeUtil.getChildren(leaf)[0];
            GraphicsAlgorithm childGA = getPictogramElementForBusinessObject(child).getGraphicsAlgorithm();
            GraphicsAlgorithm parentGA = getPictogramElementForBusinessObject(NodeUtil.getParent(leaf)).getGraphicsAlgorithm();
            
            int toMove = leafGA.getX() - childGA.getX() + (leafGA.getWidth() - childGA.getWidth()) / 2;
            moveSubTreeHorizontal(child, toMove, monitor);
            System.out.println(leaf);
         }
      }
      
      
//      resizeRectsIfNeeded(mc, monitor);
//
//      updateParents(getPictogramElementForBusinessObject(mc), OFFSET, new SubProgressMonitor(monitor, 1));
//      
      resizeRectsIfNeeded(mc, monitor);
   }
   
   /*
    * TODO
    */
   protected void updateExpand(ISEDMethodCall mc, IProgressMonitor monitor) throws DebugException {
      GraphicsAlgorithm rectGA = getPictogramElementForBusinessObject(mc, 0).getGraphicsAlgorithm();
      GraphicsAlgorithm nodeGA = getPictogramElementForBusinessObject(mc).getGraphicsAlgorithm();
      
      ISEDBranchCondition[] bcs = NodeUtil.getSortedBCs(mc);
      
      DefaultRemoveFeature drf = new DefaultRemoveFeature(getFeatureProvider());
      for(ISEDBranchCondition bc : bcs) {
         PictogramElement bcPE = getPictogramElementForBusinessObject(bc);
         removeConnections(bcPE, drf);
         drf.remove(new RemoveContext(bcPE));
      }

      removeConnections(getPictogramElementForBusinessObject(mc), drf);

      int mostLeftInParent = findMostLeftXOfBranchInParents(mc);
      
      nodeGA.setX(mostLeftInParent < rectGA.getX() ? mostLeftInParent + METOFF : rectGA.getX() + METOFF);
      
      mc.setCollapsed(false);
      
      Set<ISEDDebugNode> leafs = expandChildrenLeft(mc, 0, monitor);
      
      for(ISEDBranchCondition bc : bcs) {
         ISEDBaseMethodReturn mr = (ISEDBaseMethodReturn) bc.getChildren()[0];
         PictogramElement mrPE = getFeatureProvider().getPictogramElementForBusinessObject(mr);
         PictogramElement parentPE = getFeatureProvider().getPictogramElementForBusinessObject(NodeUtil.getParent(mr));
         
         createConnection((AnchorContainer)parentPE, (AnchorContainer)mrPE);
      }

      centerChildren(mc, new HashSet<ISEDDebugNode>(leafs), new SubProgressMonitor(monitor, 1));
      adjustRects(mc, monitor);
      updateParents(getPictogramElementForBusinessObject(mc), OFFSET, monitor);
      adjustRects(mc, monitor);
//      
      resizeRectsIfNeeded(mc, monitor);

      if(!ArrayUtil.isEmpty(mc.getCallStack())) {
         shrinkRectHeights(mc);
      }
   }
   
   /*
    * TODO
    */
   protected void shrinkRectHeights(ISEDMethodCall mc) throws DebugException {
      GraphicsAlgorithm rectGA = null;
      do
      {
         ISEDBranchCondition[] bcs = mc.getMethodReturnConditions();
         rectGA = getPictogramElementForBusinessObject(mc, 0).getGraphicsAlgorithm();
         
         int height = 0;
         for(ISEDBranchCondition bc : bcs) {
            ISEDDebugNode mr = bc.getChildren()[0];
            PictogramElement mrPE = getPictogramElementForBusinessObject(mr);
                             
            if(mrPE != null && mrPE.getGraphicsAlgorithm().getHeight() > height) {
               height = mrPE.getGraphicsAlgorithm().getHeight();
            }
         }
         
         int diff = rectGA.getY() + rectGA.getHeight() - findDeepestYInMethod((ISEDMethodCall) mc) - OFFSET - height / 2;

         if(diff != 0)
         {
            rectGA.setHeight(rectGA.getHeight() - diff);
   
            for(int i = 0; i < bcs.length; i++) {
               ISEDDebugNode mr = bcs[i].getChildren()[0];
               PictogramElement mrPE = getPictogramElementForBusinessObject(mr);
                                
               if(mrPE != null) {
                  ISEDMethodCall parentMC = ArrayUtil.isEmpty(mc.getCallStack()) ? null : (ISEDMethodCall) mc.getCallStack()[0];
                  moveSubTreeBetweenMRVertical(parentMC, mr, -diff);
               }
            }
         }

         mc = (ISEDMethodCall) (!ArrayUtil.isEmpty(mc.getCallStack()) ? mc.getCallStack()[0] : null);
      } while(mc != null);
   }
   
   /*
    * TODO
    */
//   protected int findDeepestYInMethod(ISEDMethodCall mc) throws DebugException {
//      int deepestY = 0;
//      int methodAmount = 0;
//      ISEDIterator iter = new SEDMethodPreorderIterator(mc);
//      while (iter.hasNext()) {
//         ISEDDebugElement next = iter.next();
//         
//         if(next instanceof ISEDDebugNode)
//         {
//            ISEDDebugNode nextNode = (ISEDDebugNode) next;
//            
//            if(ArrayUtil.isEmpty(nextNode.getCallStack()) && !(nextNode instanceof ISEDBranchCondition)) {
//               continue;
//            }
//            
//            if(nextNode instanceof ISEDBaseMethodReturn)
//            {
//               if(nextNode.getCallStack()[0].equals(mc)) {
//                  continue;
//               }
//            }
//            
//            PictogramElement pe = getPictogramElementForBusinessObject(nextNode);
//            if (pe != null) {
//               GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
//               if (ga.getY() + ga.getHeight() > deepestY) {
//                  deepestY = ga.getY() + ga.getHeight();
//                  
//                  if(nextNode instanceof ISEDMethodReturn) {
//                     nextNode = nextNode.getCallStack()[0];
//                  }
//                  
//                  if(!ArrayUtil.isEmpty(nextNode.getCallStack())) {
//                     int index = ArrayUtil.indexOf(nextNode.getCallStack(), mc);
//
//                     if(index != -1) {
//                        methodAmount = index; 
//                     }
//                  }
//               }
//            }
//         }
//      }
//      
//      return deepestY + methodAmount * OFFSET;
//   }
   
   /**
    * Iterates over the most right children in the Method of the given {@link ISEDDebugNode}
    * and computes the maximal x value (x + width) of the visited child {@link ISEDDebugNode}s.
    * @param node The {@link ISEDDebugNode} to start.
    * @return The most maximal x value of most right child {@link ISEDDebugNode}s.
    * @throws DebugException Occurred Exception.
    */
   private int findMostRightXInMethod(ISEDMethodCall mc, ISEDDebugNode node) throws DebugException {
      int mostRightXInSubtree = 0;
      ISEDDebugNode start = node;
      while (node != null) {
         PictogramElement pe = node instanceof ISEDMethodCall && !node.equals(start) ? getPictogramElementForBusinessObject(node, 0) : getPictogramElementForBusinessObject(node);
         if (pe != null) {
            GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
            if (ga.getX() + ga.getWidth() > mostRightXInSubtree) {
               mostRightXInSubtree = ga.getX() + ga.getWidth();
            }
         }
         // Select child for next loop iteration
         ISEDDebugNode parent = node;
         node = ArrayUtil.getLast(NodeUtil.getChildren(node, true));
         
         if(node != null && ArrayUtil.isEmpty(node.getCallStack()) && !(node instanceof ISEDBranchCondition) ||
               parent instanceof ISEDBaseMethodReturn && parent.getCallStack()[0].equals(mc)) {
            node = null;
         }
      }
      return mostRightXInSubtree;
   }
   
   /*
    * TODO
    */
   private void resizeRectsIfNeeded(ISEDMethodCall mc, IProgressMonitor monitor) throws DebugException {
      do
      {
         PictogramElement mcPE = getPictogramElementForBusinessObject(mc, 0);

         if(mcPE != null)
         {
            GraphicsAlgorithm rectGA = mcPE.getGraphicsAlgorithm();
            
            int mostLeftX = findMostLeftXInMethod(mc) - METOFF;
     
            if(mostLeftX > rectGA.getX() && !ArrayUtil.isEmpty(mc.getCallStack())) {
               rectGA.setX(mostLeftX);
            }

            rectGA.setWidth(findMostRightXInMethod(mc, mc) + METOFF - rectGA.getX());
         }
         mc = !ArrayUtil.isEmpty(mc.getCallStack()) ? (ISEDMethodCall) mc.getCallStack()[0] : null;
      } while(mc != null);
   }   
   
   /**
    * Moves all nodes in the sub tree between the given {@link ISEDMethodReturn} and
    * the next {@link ISEDMethodReturn} or {@link ISEDTermination} vertical by the given distance.
    * @param mr The {@link ISEDDebugNode} to start with.
    * @param node The {@link ISEDDebugNode} to start moving.
    * @param distance The distance to move in y direction.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception
    */
   protected void moveSubTreeBetweenMRVertical(ISEDMethodCall mc, ISEDDebugNode node, int distance) throws DebugException {
      
      ISEDIterator iter = mc == null ? new SEDPreorderIterator(node) : new SEDMethodPreorderIterator(mc, node);
      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();            
         
         if(next instanceof ISEDDebugNode) {
            
            if(next == null || next instanceof ISEDBaseMethodReturn && !next.equals(node)) {
               continue;
            }
            
            ISEDDebugNode nextNode = (ISEDDebugNode) next;
            PictogramElement pe = getPictogramElementForBusinessObject(nextNode);
            if (pe != null) {
               pe.getGraphicsAlgorithm().setY(pe.getGraphicsAlgorithm().getY() + distance);
            }
         }
      }
   }
   
   /*
    * TODO
    */
   protected ISEDDebugNode getLeafForRecenterChildren(ISEDDebugNode node, int width, IProgressMonitor monitor) throws DebugException {
      int metRets = 0;
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
                  int mostLeftX = findMostLeftXOfBranchInParents(nextNode);
                  
                  if(mostLeftX < nextGA.getX()) {
                     int moveBy = nextGA.getX() - mostLeftX;
//                     moveSubTreeHorizontal(nextNode, -moveBy + metRets * METOFF, monitor);
//                     leafGA.setX(mostLeftX);
                  }
                  return nextNode;
               }
               
               if(nextNode instanceof ISEDBaseMethodReturn) {
                  metRets++;
               }
            }
         }
      }
      
      return null;
   }
   
   protected boolean hasBiggerChild(ISEDDebugNode node, int width) throws DebugException {
      ISEDIterator iter = new SEDPreorderIterator(node);
      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();
         
         if(next instanceof ISEDDebugNode) {
            ISEDDebugNode nextNode = (ISEDDebugNode) next;
            PictogramElement nextPE = getPictogramElementForBusinessObject(nextNode);
            if(nextPE != null) {
               GraphicsAlgorithm nextGA = nextPE.getGraphicsAlgorithm();
               if(nextGA.getWidth() > width) {
                  return true;
               }
            }
         }
      }
      
      return false;
   }

   /*
    * TODO
    */
   public Set<ISEDDebugNode> expandChildrenLeft(ISEDMethodCall mc, int maxX, IProgressMonitor monitor) throws DebugException {
      Set<ISEDDebugNode> leafs = new LinkedHashSet<ISEDDebugNode>();
      ISEDIterator iter = new SEDMethodPreorderIterator(mc);

      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();
         
         // Ignore the bo, because either it is ISEDDebugTarget (the very first bo) which has no graphical representation
         // or its a parentnode which already has a graphical representation
         if(next == mc) {
            continue;
         }

         ISEDDebugNode nextNode = (ISEDDebugNode)next;
//         System.out.println(nextNode);
         PictogramElement nextPE = getPictogramElementForBusinessObject(next);
         if (nextPE == null) {
//            mist(mc, nextNode);
            createGraphicalRepresentationForNode(nextNode, OFFSET, 0);
//            bla(mc, nextNode, OFFSET, 0);
            nextPE = getPictogramElementForBusinessObject(nextNode);
            if (nextPE != null) {
               // Update maxX to make sure that ISEDDebugTargets don't overlap each other.
               GraphicsAlgorithm nextGA = nextPE.getGraphicsAlgorithm();

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
            
            if(parentGA.getX() >= nextGA.getX() + METOFF) {
               moveSubTreeHorizontal(nextNode, parentGA.getX() - nextGA.getX(), monitor);
            }
            
            int mostLeftSub = findMostLeftXInSubtree(nextNode);
            int mostRightXInPrev = findMostRightXInPreviousBranch(nextNode);
            
            if(mostRightXInPrev + OFFSET > mostLeftSub) {
               moveSubTreeHorizontal(nextNode, OFFSET - (mostLeftSub - mostRightXInPrev) , monitor);
            }
            
            int biggestWidth = findBiggestWidthInPartTreeAbove(nextNode);
            if(!hasBiggerChild(nextNode, nextGA.getWidth()) && biggestWidth > nextGA.getWidth()) {
               moveSubTreeHorizontal(nextNode, (biggestWidth - nextGA.getWidth()) / 2, monitor);
               nextGA.setX(nextGA.getX() - (biggestWidth - nextGA.getWidth()) / 2);
            }
            
            
//            moveSubTreeHorizontal(nextNode, parentGA.getX() - nextGA.getX(), monitor);
//            nextGA.setX(parentGA.getX());
//            nextGA.setX(nextGA.getX() + METOFF);
            
            if(nextGA.getY() < parentGA.getY() + parentGA.getHeight() + OFFSET) {
               moveSubTreeVertical(nextNode, parentGA.getY() + parentGA.getHeight() + OFFSET - nextGA.getY());
               updateAllMethodRectHeights((ISEDMethodCall) nextNode.getCallStack()[0], nextGA, nextNode instanceof ISEDBaseMethodReturn);
            }
            
            if(!ArrayUtil.isEmpty(NodeUtil.getChildren(nextNode))) {
               ISEDDebugNode leaf = getLeafForRecenterChildren(nextNode, nextGA.getWidth(), monitor); 
               if(leaf != null) {
                  leafs.add(leaf);
                  continue;
//                  int mostLeftX = findMostLeftXOfBranchInParents(leaf);
//                  GraphicsAlgorithm leafGA = getPictogramElementForBusinessObject(leaf).getGraphicsAlgorithm();
//                  if(mostLeftX < leafGA.getX()) {
//                     int moveBy = leafGA.getX() - mostLeftX;
//                     moveSubTreeHorizontal(leaf, -moveBy, monitor);
////                     leafGA.setX(mostLeftX);
//                  }
               }
               
//               ISEDDebugNode subNode = NodeUtil.getChildren(nextNode)[0];
//               PictogramElement subNodePE = getPictogramElementForBusinessObject(subNode);
//               GraphicsAlgorithm subNodeGA = subNodePE.getGraphicsAlgorithm();
//               
//               if(nextGA.getWidth() < subNodeGA.getWidth()) {
//                  int moveBy = nextGA.getX() + nextGA.getWidth() / 2 - subNodeGA.getWidth() / 2 - subNodeGA.getX();
//                  moveSubTreeHorizontal(subNode, moveBy, monitor);
//               }
            }

            leafs.add(nextNode);
         }
      }
      return leafs;
   }
   
   /**
    * This function removes all children and connections of the given node, until
    * there are no more children or {@link ISEDMethodReturn} is reached and returns
    * all found MethodReturns.
    * @param ISEDDebugNode node The current node
    * @return Set<ISEDDebugNode> methodCloses Contains all MethodReturns
    * @throws DebugException
    */
   private void removeChildren(ISEDMethodCall node, ISEDMethodCall mc) throws DebugException {
      DefaultRemoveFeature drf = new DefaultRemoveFeature(getFeatureProvider());
      ISEDIterator iter = new SEDMethodPreorderIterator(node);
      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();
         
         if(next.equals(mc)) {
            continue;
         }
         
         if(next instanceof ISEDDebugNode)
         {
            ISEDDebugNode nextNode = (ISEDDebugNode) next;

            PictogramElement[] pes = getFeatureProvider().getAllPictogramElementsForBusinessObject(nextNode);
            
            if(pes == null || nextNode instanceof ISEDBaseMethodReturn && nextNode.getCallStack()[0] == mc ||
                 !(nextNode instanceof ISEDBranchCondition) && ArrayUtil.isEmpty(nextNode.getCallStack())) {
               continue;
            }

            for(PictogramElement pe : pes)
            {
               if(!(nextNode instanceof ISEDMethodCall)) {
                  removeConnections(pe, drf);
               }
               drf.remove(new RemoveContext(pe));
            }
         }
      }
   }
   
   /*
    * TODO
    */
   private void removeConnections(PictogramElement pe) {
      removeConnections(pe, new DefaultRemoveFeature(getFeatureProvider()));
   }

   /*
    * TODO
    */
   private void removeConnections(PictogramElement pe, DefaultRemoveFeature drf) {
      List<Connection> cons = Graphiti.getPeService().getOutgoingConnections((AnchorContainer) pe);
   
      for(Connection con : cons)
         drf.remove(new RemoveContext(con));
   }
   
   /*
    * TODO
    */
   private void createConnection(AnchorContainer startAC, AnchorContainer endAC) {
      IPeCreateService peCreateService = Graphiti.getPeCreateService();
      IGaService gaService = Graphiti.getGaService();

      Connection connection = peCreateService.createFreeFormConnection(getDiagram());
      connection.setStart(startAC.getAnchors().get(0));
      connection.setEnd(endAC.getAnchors().get(0));
 
      ConnectionDecorator cd = peCreateService.createConnectionDecorator(connection, false, 1.0, true);
      Polyline arrow = gaService.createPolyline(cd, new int[] {-10, 5, 0, 0, -10, -5});
      arrow.setStyle(ExecutionTreeStyleUtil.getStyleForParentConnection(getDiagram()));

      Polyline polyline = gaService.createPolyline(connection);
      polyline.setStyle(ExecutionTreeStyleUtil.getStyleForParentConnection(getDiagram()));
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean canUpdateBusinessObject(Object businessObject) {
      return businessObject instanceof ISEDMethodCall;
   }
}