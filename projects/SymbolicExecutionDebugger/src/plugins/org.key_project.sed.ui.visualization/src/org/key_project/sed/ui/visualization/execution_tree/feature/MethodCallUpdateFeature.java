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
   
   protected void updateCollapse(ISEDMethodCall mc, IProgressMonitor monitor) throws DebugException {
      GraphicsAlgorithm rectGA = getPictogramElementForBusinessObject(mc, 0).getGraphicsAlgorithm();
      GraphicsAlgorithm nodeGA = getPictogramElementForBusinessObject(mc).getGraphicsAlgorithm();
      
      ISEDBranchCondition[] bcs = NodeUtil.getSortedBCs(mc);

      removeChildren(mc, mc);
      removeConnections(getPictogramElementForBusinessObject(mc));
      
      mc.setCollapsed(true);

      int maxX = 0;
      boolean need2Move = true, singleReturn = false;
      Set<ISEDDebugNode> leafs = new HashSet<ISEDDebugNode>();
      
      if(bcs.length == 1)
      {
         ISEDMethodReturn mr = (ISEDMethodReturn) bcs[0].getChildren()[0];
         PictogramElement mrPE = getPictogramElementForBusinessObject(mr);
         GraphicsAlgorithm mrGA = mrPE.getGraphicsAlgorithm();
         
         int above = findBiggestWidthInPartTreeAbove(mr);
         
         if(above < mrGA.getWidth()) {
            singleReturn = true;
            nodeGA.setX(rectGA.getX() + METOFF);
         }
      }
      else {
         leafs.add(mc);
         nodeGA.setX(rectGA.getX() + METOFF);
      }

      for(ISEDBranchCondition bc : bcs)
      {
         createGraphicalRepresentationForNode(bc, OFFSET, maxX);
         
         PictogramElement bcPE = getFeatureProvider().getPictogramElementForBusinessObject(bc);
         GraphicsAlgorithm bcGA = bcPE.getGraphicsAlgorithm();

         ISEDMethodReturn mr = (ISEDMethodReturn) bc.getChildren()[0];
         PictogramElement mrPE = getFeatureProvider().getPictogramElementForBusinessObject(mr);
         GraphicsAlgorithm mrGA = mrPE.getGraphicsAlgorithm();

         int widthDiff = bcGA.getX() + bcGA.getWidth() - mrGA.getX() - mrGA.getWidth();

         if(bcGA.getWidth() < mrGA.getWidth())
         {
            bcGA.setX(mrGA.getX() + (mrGA.getWidth() - bcGA.getWidth()) / 2);
            need2Move = false;
         }

         maxX = findMostRightXInSubtree(bc) + OFFSET;
         
         int hMove = 0;
         
         if(need2Move)
         {
            hMove = (bcGA.getX() - mrGA.getX() + widthDiff) / 2;
            moveSubTreeHorizontal(mr, hMove, new SubProgressMonitor(monitor, 1));
         }

         createConnection((AnchorContainer)bcPE, (AnchorContainer)mrPE);
         
         if(singleReturn) {
            leafs.add((bcGA.getWidth() > mrGA.getWidth() ? bc : mr));
         }
      }

      shrinkRectHeights(mc);
      centerChildren(leafs, new SubProgressMonitor(monitor, 1));
      monitor.worked(1);
      
//      for(ISEDBranchCondition bc : bcs) {
//         ISEDMethodReturn mr = (ISEDMethodReturn) NodeUtil.getChildren(bc)[0];
//         PictogramElement mrPE = getFeatureProvider().getPictogramElementForBusinessObject(mr);
//
//         updateParents(mrPE, OFFSET, new SubProgressMonitor(monitor, 1));
//         monitor.worked(1);
//      }
      
      resizeRectsIfNeeded(mc);
   }
   
   protected void updateExpand(ISEDMethodCall mc, IProgressMonitor monitor) throws DebugException {
      GraphicsAlgorithm rectGA = getPictogramElementForBusinessObject(mc, 0).getGraphicsAlgorithm();
      GraphicsAlgorithm nodeGA = getPictogramElementForBusinessObject(mc).getGraphicsAlgorithm();
      
      ISEDBranchCondition[] bcs = NodeUtil.getSortedBCs(mc);
      
      nodeGA.setX(rectGA.getX());
      
      DefaultRemoveFeature drf = new DefaultRemoveFeature(getFeatureProvider());
      for(ISEDBranchCondition bc : bcs) {
         ISEDMethodReturn mr = (ISEDMethodReturn) bc.getChildren()[0];
         PictogramElement mrPE = getFeatureProvider().getPictogramElementForBusinessObject(mr);
         GraphicsAlgorithm mrGA = mrPE.getGraphicsAlgorithm();

         ISEDDebugNode previousSibling = ArrayUtil.getPrevious(NodeUtil.getChildren(NodeUtil.getParent(bc), true), bc);

         boolean wasMoved = false;
         if (previousSibling != null) {
            int subTreeWidth = findMostRightXInSubtree(NodeUtil.getChildren(previousSibling)[0]);
            if (subTreeWidth > -1) {
               int horMove = subTreeWidth + OFFSET;
               //Math.abs sollte die Pos < 0 sein
               moveSubTreeBetweenMRHorizontal(mr, mr, - mrGA.getX() + horMove);
               wasMoved = true;
            }
         }
         
         int above = findBiggestWidthInPartTreeAbove(mc);

         if(!wasMoved && above < mrGA.getWidth()) {
            int maxXOnParents = findMostLeftXOfBranchInParents(mr);
            int maxXInChildren = findMostLeftXInSubtree(mr);
            int maxXOfBranch = maxXOnParents < maxXInChildren ? maxXOnParents : maxXInChildren;
            moveSubTreeBetweenMRHorizontal(mr, mr, - mrGA.getX() + maxXOfBranch);
         }
         
         PictogramElement bcPE = getFeatureProvider().getPictogramElementForBusinessObject(bc);
         removeConnections(bcPE, drf);
         drf.remove(new RemoveContext(bcPE));
      }

      removeConnections(getPictogramElementForBusinessObject(mc), drf);
      
      mc.setCollapsed(false);
      
//      updateChildren(getPictogramElementForBusinessObject(mc), OFFSET, monitor);
//      updateChildrenLeftAligned(mc, monitor, OFFSET, 0);
      Set<ISEDDebugNode> leafs = kacke(mc, 0, monitor);//updateChildrenLeftAligned(mc, monitor, OFFSET, 0);
      centerMethod(mc, leafs, monitor);
//      updateParents(getPictogramElementForBusinessObject(mc), OFFSET, monitor);
//      update(new UpdateContext(getPictogramElementForBusinessObject(mc)));

      leafs = new HashSet<ISEDDebugNode>();
      Set<ISEDDebugNode> leafSubtree = new HashSet<ISEDDebugNode>();
      for(ISEDBranchCondition bc : bcs) {
         ISEDMethodReturn mr = (ISEDMethodReturn) bc.getChildren()[0];
         PictogramElement mrPE = getFeatureProvider().getPictogramElementForBusinessObject(mr);
         PictogramElement parentPE = getFeatureProvider().getPictogramElementForBusinessObject(NodeUtil.getParent(mr));
         
         createConnection((AnchorContainer)parentPE, (AnchorContainer)mrPE);
         
//         if(!ArrayUtil.isEmpty(NodeUtil.getChildren(mr))) {
//            ISEDDebugNode leaf = getLeafForRecenterChildren(mr, mrPE.getGraphicsAlgorithm().getWidth()); 
//            if(leaf != null) {
//               leafs.add(leaf);
//               
//               int mostLeftX = findMostLeftXOfBranchInParents(leaf);
//               GraphicsAlgorithm leafGA = getPictogramElementForBusinessObject(leaf).getGraphicsAlgorithm();
//               if(mostLeftX < leafGA.getX()) {
////                  leafGA.setX(mostLeftX);
//               }
//            }
//            
//            ISEDDebugNode subNode = NodeUtil.getChildren(mr)[0];
//            PictogramElement subNodePE = getPictogramElementForBusinessObject(subNode);
//            GraphicsAlgorithm subNodeGA = subNodePE.getGraphicsAlgorithm();
//            GraphicsAlgorithm parentGA = getPictogramElementForBusinessObject(NodeUtil.getParent(subNode)).getGraphicsAlgorithm();
//            
//            if(parentGA.getWidth() < subNodeGA.getWidth()) {
//               int moveBy = parentGA.getX() + parentGA.getWidth() / 2 - subNodeGA.getWidth() / 2 - subNodeGA.getX();
////               moveSubTreeHorizontal(subNode, moveBy, monitor);
//            }
//            
////            leafSubtree.add(NodeUtil.getChildren(mr)[0]);
//         }
      }
      
      if(!leafs.isEmpty()) {
//         centerChildren(leafs, new SubProgressMonitor(monitor, 1));
//         centerMethod(mc, leafs, monitor);
      }
      
//      for(ISEDDebugNode subNode : leafSubtree)
//      {
//         PictogramElement subNodePE = getPictogramElementForBusinessObject(subNode);
//         GraphicsAlgorithm subNodeGA = subNodePE.getGraphicsAlgorithm();
//         GraphicsAlgorithm parentGA = getPictogramElementForBusinessObject(NodeUtil.getParent(subNode)).getGraphicsAlgorithm();
//         
//         int moveBy = parentGA.getX() + parentGA.getWidth() / 2 - subNodeGA.getWidth() / 2 - subNodeGA.getX();
//         moveSubTreeHorizontal(subNode, moveBy, monitor);
//      }

//      for(ISEDDebugNode leaf : leafs) {
//         PictogramElement leafPE = getFeatureProvider().getPictogramElementForBusinessObject(leaf);
//         updateParents(leafPE, OFFSET, new SubProgressMonitor(monitor, 1));
//         System.out.println(leaf);
//      }
      
      resizeRectsIfNeeded(mc);

      if(!ArrayUtil.isEmpty(mc.getCallStack())) {
         shrinkRectHeights(mc);
      }
   }
   
   protected void centerMethod(ISEDMethodCall mc, final Set<ISEDDebugNode> leafs, IProgressMonitor monitor) throws DebugException {
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
         // Compute new x margin to center current branch under his children 
         int xMargin;
         int xStart;
         boolean removeChildrenRequired = false;

         ISEDDebugNode[] children = NodeUtil.getChildren(next);
//         if (!ArrayUtil.isEmpty(getChildren(next)))
         if (!ArrayUtil.isEmpty(children) && children.length > 1)
         {
            ISEDDebugNode firstChild = ArrayUtil.getFirst(children);
            ISEDDebugNode lastChild = ArrayUtil.getLast(children);
            PictogramElement firstChildPE = getPictogramElementForBusinessObject(firstChild);
            PictogramElement lastChildPE = getPictogramElementForBusinessObject(lastChild);
            int childWidth = lastChildPE.getGraphicsAlgorithm().getX() + lastChildPE.getGraphicsAlgorithm().getWidth() - 
                             firstChildPE.getGraphicsAlgorithm().getX();

            xMargin = (childWidth - nextPE.getGraphicsAlgorithm().getWidth()) / 2;
            xStart = firstChildPE.getGraphicsAlgorithm().getX();
            
//            System.out.println("XM: " + xMargin + ", XS: " + xStart + ", NPEX: " + nextPE.getGraphicsAlgorithm().getX());
            
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
         
//         System.out.println("XM: " + xMargin + ", XS: " + xStart + ", X: " + nextPE.getGraphicsAlgorithm().getX());
         
         // Go back to root or branch split and collect descendants while computing max width
         // If a parent node has more than one child it is treated as leaf node in a further iteration by adding it to leafs
         List<PictogramElement> descendantsPE = new LinkedList<PictogramElement>();
         int maxWidth = 0;
//         boolean maxInitialised = false;
         ISEDDebugNode current = next;
         PictogramElement currentPE = nextPE;

         boolean locked = false;
         int xOff = 0;
         do {
//            System.out.println("Current: " + current);
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
               if (ArrayUtil.isLast(NodeUtil.getChildren(current), child)) {  // Update parent only if all of his branches are correctly centered
                  leafs.add(current);
//                  System.out.println(current);
               }
               current = null;
            }
         } while (current != null && !monitor.isCanceled());

         // Center collected descendants based on the computed maximal element width
         boolean cool = false;
         Iterator<PictogramElement> descendantIter = descendantsPE.iterator();
         while (descendantIter.hasNext() && !monitor.isCanceled()) {
            PictogramElement pe = descendantIter.next();
            GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
            int newX = xMargin + xStart + xOff + (maxWidth - ga.getWidth()) / 2; 
            ga.setX(newX);
//            System.out.println("NEWX: " + (xMargin + xStart + (maxWidth - ga.getWidth()) / 2));

            ISEDDebugNode node = (ISEDDebugNode) getBusinessObjectForPictogramElement(pe);

            if(!node.equals(mc) && !ArrayUtil.isEmpty(node.getCallStack()))
            {
               ISEDDebugNode methodCall = node.getCallStack()[0];
               PictogramElement mcPE = getPictogramElementForBusinessObject(methodCall, 0);
               GraphicsAlgorithm mcGA = mcPE.getGraphicsAlgorithm();
               
               if(node instanceof ISEDMethodCall)// && ArrayUtil.isEmpty(methodCall.getCallStack()))
               {
//                  System.out.println(node);
                  GraphicsAlgorithm rectGA = getPictogramElementForBusinessObject(node, 0).getGraphicsAlgorithm();
                  if(rectGA.getX() <= mcGA.getX()) {
                     moveSubTreeHorizontal(node, METOFF, monitor);
//                     moveMethodBodyHorizontal((ISEDMethodCall) node, METOFF);
//                     moveSubTreeBetweenMRHorizontal(methodCall, node, METOFF);
                     
                     if(!cool) {
                        rectGA.setX(rectGA.getX() - METOFF);
                        moveSubTreeHorizontal(node, METOFF, monitor);
//                        moveMethodBodyHorizontal((ISEDMethodCall) node, METOFF);
//                        moveSubTreeBetweenMRHorizontal(methodCall, node, METOFF);
//                        rectGA.setX(rectGA.getX() + METOFF / 2);
//                        moveSubTreeHorizontal(node, METOFF, monitor);
                        xOff += METOFF;
                        cool = true;
                     }
//                     moveRighterNodes(node, METOFF * metAm, monitor);
                     updateParents(pe, OFFSET, monitor);
//                     ga.setX(mcGA.getX() + METOFF);
                     xOff += METOFF;
//                     cool = true;
                  }
               }

//               if(ga.getX() < mcGA.getX() + METOFF)
//               {
//                  if(!ArrayUtil.isEmpty(methodCall.getCallStack()))
//                  {
//                     ISEDDebugNode outerMethod = methodCall.getCallStack()[0];
//                     PictogramElement outerPE = getPictogramElementForBusinessObject(outerMethod, 0);
//                     GraphicsAlgorithm outerGA = outerPE.getGraphicsAlgorithm();
//                     
//                     if(outerGA.getX() + METOFF <= mcGA.getX())
//                     {
//                        if(ga.getX() < outerGA.getX() + METOFF) {
//                           mcGA.setX(outerGA.getX());
//                           ga.setX(mcGA.getX() + METOFF);
//                           xOff += METOFF;
//                        }
//                        else {
//                           if(ga.getX() - METOFF <= outerGA.getX() + METOFF) {
//                              mcGA.setX(outerGA.getX() + METOFF);
//                              moveSubTreeHorizontal(node, METOFF, monitor);
////                              ga.setX(ga.getX() + METOFF);
//                              xOff += METOFF;
//                           }
//                           else {
//                              mcGA.setX(ga.getX() - METOFF);
//                           }
//                        }
//                     }
//                  }
//               }

               updateAllMethodRectWidths((ISEDMethodCall) methodCall, ga);
            }
//            if(!ArrayUtil.isEmpty(node.getCallStack()))
//            {
//               ISEDDebugNode methodCall = node.getCallStack()[0];
//               PictogramElement mcPE = getPictogramElementForBusinessObject(methodCall, 0);
//               GraphicsAlgorithm mcGA = mcPE.getGraphicsAlgorithm();
//               
//               if(node instanceof ISEDMethodCall)
//               {
//                  GraphicsAlgorithm rectGA = getPictogramElementForBusinessObject(node, 0).getGraphicsAlgorithm();
//                  if(rectGA.getX() <= mcGA.getX()) {
////                     rectGA.setX(rectGA.getX() + METOFF);
//                     moveMethodBodyHorizontal((ISEDMethodCall) node, METOFF);
////                     moveSubTreeHorizontal(node, METOFF, monitor);
////                     moveRighterNodes(node, METOFF * metAm, monitor);
////                     updateParents(pe, OFFSET, monitor);
////                     ga.setX(mcGA.getX() + METOFF);
//                     xOff += METOFF;
////                     cool = true;
//                  }
//               }
//
//               if(ga.getX() < mcGA.getX() + METOFF)
//               {
//                  if(!ArrayUtil.isEmpty(methodCall.getCallStack()))
//                  {
//                     ISEDDebugNode outerMethod = methodCall.getCallStack()[0];
//                     PictogramElement outerPE = getPictogramElementForBusinessObject(outerMethod, 0);
//                     GraphicsAlgorithm outerGA = outerPE.getGraphicsAlgorithm();
//                     
//                     if(outerGA.getX() + METOFF <= mcGA.getX())
//                     {
//                        if(ga.getX() < outerGA.getX() + METOFF) {
//                           mcGA.setX(outerGA.getX());
//                           ga.setX(mcGA.getX() + METOFF);
//                           xOff += METOFF;
//                        }
//                        else {
//                           if(ga.getX() - METOFF <= outerGA.getX() + METOFF) {
//                              mcGA.setX(outerGA.getX() + METOFF);
//                              ga.setX(ga.getX() + METOFF);
//                              xOff += METOFF;
//                           }
//                           else {
//                              mcGA.setX(ga.getX() - METOFF);
//                           }
//                        }
//                     }
//                  }
//               }
//
//               updateAllMethodRectWidths((ISEDMethodCall) methodCall, ga);
//            }
         }
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
      }
   }
   
   protected void shrinkRectHeights(ISEDMethodCall mc) throws DebugException {
      GraphicsAlgorithm prevRectGA, rectGA = null;
      do
      {
         ISEDBranchCondition[] bcs = mc.getMethodReturnConditions();
         prevRectGA = rectGA;
         rectGA = getPictogramElementForBusinessObject(mc, 0).getGraphicsAlgorithm();
         
         int height = -1;
         for(ISEDBranchCondition bc : bcs) {
            ISEDDebugNode mr = bc.getChildren()[0];
            PictogramElement mrPE = getPictogramElementForBusinessObject(mr);
                             
            if(mrPE != null && mrPE.getGraphicsAlgorithm().getHeight() > height) {
               height = mrPE.getGraphicsAlgorithm().getHeight();
            }
         }
         
         int diff = 0;

         if(height > -1) {
            diff = rectGA.getY() + rectGA.getHeight() - findDeepestYInMethod((ISEDMethodCall) mc) - OFFSET - height / 2;
         }
         else {
            diff = rectGA.getY() + rectGA.getHeight() - prevRectGA.getY() - prevRectGA.getHeight() - OFFSET;
         }
         
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
            
   //         ISEDTermination[] terminations = mc.getThread().getTerminations();
   //         for(ISEDTermination t : terminations)
   //         {
   //            if(t instanceof ISEDExceptionalTermination)
   //            {
   //               ISEDDebugNode parent = t.getParent();
   //               if(parent.getCallStack() != null && parent.getCallStack().length > 0)
   //               {
   //                  PictogramElement tPE = getPictogramElementForBusinessObject(t);
   //                  
   //                  if(tPE != null){
   //                     moveSubTreeVertical(t, -diff);
   //                  }
   //               }  
   //            }
   //         }
         mc = (ISEDMethodCall) (!ArrayUtil.isEmpty(mc.getCallStack()) ? mc.getCallStack()[0] : null);
      } while(mc != null);
   }
   
   protected int findDeepestYInMethod(ISEDMethodCall mc) throws DebugException {
      int deepestY = 0;
      ISEDIterator iter = new SEDMethodPreorderIterator(mc);
      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();
         
         if(next instanceof ISEDDebugNode)
         {
            ISEDDebugNode nextNode = (ISEDDebugNode) next;
            
            if(ArrayUtil.isEmpty(nextNode.getCallStack()) && !(nextNode instanceof ISEDBranchCondition)) {
               continue;
            }
            
            if(nextNode instanceof ISEDMethodReturn)
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
               }
            }
         }
      }

      return deepestY;
   }
   
   protected ISEDDebugNode findDeepestNodeInMethod(ISEDMethodCall mc) throws DebugException {
      ISEDDebugNode node = null;
      int deepestY = 0;
      ISEDIterator iter = new SEDMethodPreorderIterator(mc);
      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();
         
         if(next instanceof ISEDDebugNode)
         {
            ISEDDebugNode nextNode = (ISEDDebugNode) next;
            
            if(ArrayUtil.isEmpty(nextNode.getCallStack()) && !(nextNode instanceof ISEDBranchCondition)) {
               continue;
            }
            
            if(nextNode instanceof ISEDMethodReturn)
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
                  node = nextNode;
               }
            }
         }
      }

      return node;
   }
   
   /**
    * Iterates over the most right children in the Method of the given {@link ISEDDebugNode}
    * and computes the maximal x value (x + width) of the visited child {@link ISEDDebugNode}s.
    * @param node The {@link ISEDDebugNode} to start.
    * @return The most maximal x value of most right child {@link ISEDDebugNode}s.
    * @throws DebugException Occurred Exception.
    */
   protected int findMostRightXInMethod(ISEDMethodCall mc, ISEDDebugNode node) throws DebugException {
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
               parent instanceof ISEDMethodReturn && parent.getCallStack()[0].equals(mc)) {
            node = null;
         }
      }
      return mostRightXInSubtree;
   }
   
   /**
    * Iterates over the most right children in the Method of the given {@link ISEDDebugNode}
    * and computes the maximal x value (x + width) of the visited child {@link ISEDDebugNode}s.
    * @param node The {@link ISEDDebugNode} to start.
    * @return The most maximal x value of most right child {@link ISEDDebugNode}s.
    * @throws DebugException Occurred Exception.
    */
   protected int findMostLeftXInMethod(ISEDDebugNode node) throws DebugException {
      int mostLeftXInSubtree = -1;
      ISEDDebugNode mc = node;
      while (node != null) {
         PictogramElement pe = getPictogramElementForBusinessObject(node);
         if (pe != null) {
            GraphicsAlgorithm ga = pe.getGraphicsAlgorithm();
            if (ga.getX() < mostLeftXInSubtree || mostLeftXInSubtree == -1) {
               mostLeftXInSubtree = ga.getX();
            }
         }
         // Select child for next loop iteration
         ISEDDebugNode parent = node;
         node = ArrayUtil.getLast(NodeUtil.getChildren(node));
         
         if(node != null && ArrayUtil.isEmpty(node.getCallStack()) && !(node instanceof ISEDBranchCondition) ||
               parent instanceof ISEDMethodReturn && parent.getCallStack()[0].equals(mc)) {
            node = null;
         }
      }
      return mostLeftXInSubtree;
   }
   
   protected int findBiggestWidthInPartTreeAbove(ISEDDebugNode start) throws DebugException {
      ISEDDebugNode node = start;
      int x = -1;
      do
      {
         node = NodeUtil.getParent(node);
         
         if(node == null || NodeUtil.getChildren(node).length != 1) {
            break;
         }
         
         PictogramElement nodePE = getPictogramElementForBusinessObject(node);
         if(nodePE != null)
         {
            GraphicsAlgorithm nodeGA = nodePE.getGraphicsAlgorithm();
            if(nodeGA.getWidth() > x || x == -1) {
               x = nodeGA.getWidth();
            }
         }
      } while(true);
      return x;
   }
   
   protected int findMostLeftXInPartTreeUnder(ISEDDebugNode start) throws DebugException {
      ISEDDebugNode node = start;
      int x = -1;

      while(true)
      {
         PictogramElement nodePE = getPictogramElementForBusinessObject(node);
         if(nodePE != null)
         {
            GraphicsAlgorithm nodeGA = nodePE.getGraphicsAlgorithm();
            if(nodeGA.getX() < x || x == -1) {
               x = nodeGA.getX();
            }
         }
         
         if(NodeUtil.getChildren(node).length != 1) {
            break;
         }
         
         node = ArrayUtil.getFirst(NodeUtil.getChildren(node));
      }

      return x;
   }
   
   protected Set<ISEDDebugNode> gatherLeafsOfMethod(ISEDMethodCall mc) throws DebugException {
      Set<ISEDDebugNode> leafs = new LinkedHashSet<ISEDDebugNode>();
      ISEDIterator iter = new SEDMethodPreorderIterator(mc);
      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();
         
         if(next instanceof ISEDDebugNode)
         {
            ISEDDebugNode nextNode = (ISEDDebugNode) next;
            ISEDDebugNode[] children = NodeUtil.getChildren(nextNode); 
            if(ArrayUtil.isEmpty(children) ||
                  ArrayUtil.isEmpty(children[0].getCallStack()) && !(children[0] instanceof ISEDBranchCondition) ||
                  getPictogramElementForBusinessObject(children[0]) == null)
            {
               leafs.add(nextNode);
            }
         }
      }
      return leafs;
   }
   
   protected void resizeRectsIfNeeded(ISEDMethodCall mc) throws DebugException {
      do
      {
         PictogramElement mcPE = getPictogramElementForBusinessObject(mc, 0);

         if(mcPE != null)
         {
            GraphicsAlgorithm rectGA = mcPE.getGraphicsAlgorithm();
            
//                  int mostLeftX = findMostLeftXInMethod(mc);
//                  if(mostLeftX > rectGA.getX()) {
//                     rectGA.setX(mostLeftX);
//                  }
            
//            int mostRightX = findMostRightXInMethod(mc) + METOFF;
            rectGA.setWidth(findMostRightXInMethod(mc, mc) + METOFF - rectGA.getX());
//            if(mostRightX < rectGA.getX() + rectGA.getWidth()) {
//               int diff = rectGA.getX() + rectGA.getWidth() - findMostRightXInMethod(mc) + METOFF;
//               rectGA.setWidth(rectGA.getWidth() - diff);
//               System.out.println("D: " + diff + ", W: " + rectGA.getWidth());
//            }
         }
         mc = !ArrayUtil.isEmpty(mc.getCallStack()) ? (ISEDMethodCall) mc.getCallStack()[0] : null;
      } while(mc != null);
   }
   
   protected int computeCollapsedHeight(ISEDMethodCall mc) throws DebugException {
      int height = 0;
      ISEDBranchCondition[] bcs = NodeUtil.getSortedBCs(mc);
      GraphicsAlgorithm mcGA = getPictogramElementForBusinessObject(mc).getGraphicsAlgorithm();
      
      for(ISEDBranchCondition bc : bcs)
      {
         if(NodeUtil.getChildren(bc)[0] instanceof ISEDTermination) {
            continue;
         }
         
         GraphicsAlgorithm bcGA = getPictogramElementForBusinessObject(bc).getGraphicsAlgorithm();
         GraphicsAlgorithm childGA = getPictogramElementForBusinessObject(NodeUtil.getChildren(bc)[0]).getGraphicsAlgorithm();
         
         int comHeight = mcGA.getHeight() / 2 + bcGA.getHeight() + childGA.getHeight() / 2 + 2 * OFFSET; 
         
         if(comHeight > height) {
            height = comHeight;
         }
      }
      
      return height;
   }
   
   /**
    * Moves all nodes in the sub tree between the given {@link ISEDMethodReturn} and
    * the next {@link ISEDMethodReturn} or {@link ISEDTermination} horizontal by the given distance.
    * @param mr The {@link ISEDDebugNode} to start with.
    * @param node The {@link ISEDDebugNode} to start moving.
    * @param distance The distance to move in x direction.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception
    */
//   protected void moveSubTreeBetweenMRHorizontal(ISEDMethodCall mc, ISEDDebugNode node, int distance) throws DebugException {
//      
//      ISEDIterator iter = mc == null ? new SEDPreorderIterator(node) : new SEDMethodPreorderIterator(mc, node);
//      while (iter.hasNext()) {
//         ISEDDebugElement next = iter.next();
//         
//         if(next instanceof ISEDDebugNode) {
//            ISEDDebugNode nextNode = (ISEDDebugNode) next;
//            PictogramElement pe = getPictogramElementForBusinessObject(nextNode);
//            if (pe != null) {
//               pe.getGraphicsAlgorithm().setX(pe.getGraphicsAlgorithm().getX() + distance);
//            }
//         }
//      }
//   }
   protected void moveSubTreeBetweenMRHorizontal(ISEDDebugNode mr, ISEDDebugNode node, int distance) throws DebugException {
      
      if(node == null || node instanceof ISEDMethodReturn && !node.equals(mr))
         return;
      
      PictogramElement pe = getPictogramElementForBusinessObject(node);
      if (pe != null) {
         pe.getGraphicsAlgorithm().setX(pe.getGraphicsAlgorithm().getX() + distance);
      }
      
      for(ISEDDebugNode child : NodeUtil.getChildren(node)) {
         moveSubTreeBetweenMRHorizontal(mr, child, distance);
      }
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
            
            if(next == null || next instanceof ISEDMethodReturn && !next.equals(node)) {
               continue;
            }
            
            ISEDDebugNode nextNode = (ISEDDebugNode) next;
            PictogramElement pe = getPictogramElementForBusinessObject(nextNode);
            if (pe != null) {
               pe.getGraphicsAlgorithm().setY(pe.getGraphicsAlgorithm().getY() + distance);
            }
         }
      }
      
//      if(node == null || node instanceof ISEDMethodReturn && !node.equals(mr))
//         return;
      
//      PictogramElement pe = getPictogramElementForBusinessObject(node);
//      if (pe != null) {
//         pe.getGraphicsAlgorithm().setY(pe.getGraphicsAlgorithm().getY() + distance);
//      }
      
//      for(ISEDDebugNode child : NodeUtil.getChildren(node)) {
//         moveSubTreeBetweenMRVertical(mr, child, distance);
//      }
   }
//   protected void moveSubTreeBetweenMRVertical(ISEDDebugNode mr, ISEDDebugNode node, int distance) throws DebugException {
//      
//      ISEDIterator iter = new SEDMethodPreorderIterator(mr, node);
//      
//      if(node == null || node instanceof ISEDMethodReturn && !node.equals(mr))
//         return;
//      
//      PictogramElement pe = getPictogramElementForBusinessObject(node);
//      if (pe != null) {
//         pe.getGraphicsAlgorithm().setY(pe.getGraphicsAlgorithm().getY() + distance);
//      }
//      
//      for(ISEDDebugNode child : NodeUtil.getChildren(node)) {
//         moveSubTreeBetweenMRVertical(mr, child, distance);
//      }
//   }
   
   protected void moveMethodBodyHorizontal(ISEDMethodCall mc, int distance) throws DebugException {
      ISEDIterator iter = new SEDMethodPreorderIterator(mc, mc);
      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();            
         
         if(next instanceof ISEDDebugNode) {
            
//            if(next instanceof ISEDMethodReturn && ((ISEDDebugNode) next).getCallStack()[0].equals(mc)) {
//               continue;
//            }
            
            ISEDDebugNode nextNode = (ISEDDebugNode) next;
            PictogramElement pe = getPictogramElementForBusinessObject(nextNode);
            if (pe != null) {
               pe.getGraphicsAlgorithm().setX(pe.getGraphicsAlgorithm().getX() + distance);
               
               if(nextNode instanceof ISEDMethodCall) {
                  pe = getPictogramElementForBusinessObject(nextNode, 0);
                  pe.getGraphicsAlgorithm().setX(pe.getGraphicsAlgorithm().getX() + distance);
               }
            }
         }
      }
   }
   
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
                     moveSubTreeHorizontal(nextNode, -moveBy + metRets * METOFF, monitor);
//                     leafGA.setX(mostLeftX);
                  }
                  return nextNode;
               }
               
               if(!nextNode.equals(node) && nextNode instanceof ISEDMethodReturn) {
                  metRets++;
               }
            }
         }
      }
      
      return null;
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
            
            if(pes == null || nextNode instanceof ISEDMethodReturn && nextNode.getCallStack()[0] == mc ||
                 !(nextNode instanceof ISEDBranchCondition) &&
                 !(nextNode instanceof ISEDExceptionalTermination) && ArrayUtil.isEmpty(nextNode.getCallStack())) {
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
   
   private void removeConnections(PictogramElement pe) {
      removeConnections(pe, new DefaultRemoveFeature(getFeatureProvider()));
   }

   private void removeConnections(PictogramElement pe, DefaultRemoveFeature drf) {
      List<Connection> cons = Graphiti.getPeService().getOutgoingConnections((AnchorContainer) pe);
   
      for(Connection con : cons)
         drf.remove(new RemoveContext(con));
   }
   
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
   
   private Set<ISEDDebugNode> kacke(ISEDMethodCall mc, int maxX, IProgressMonitor monitor) throws DebugException {
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
            mist(mc, nextNode);
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
                  updateAllMethodRectHeights(node, nextGA, nextNode instanceof ISEDMethodReturn);
               }
            }
            if (ArrayUtil.isEmpty(NodeUtil.getChildren(nextNode))) {
               leafs.add(nextNode);
            }
         }
         else if((nextNode instanceof ISEDMethodReturn ||
                  nextNode instanceof ISEDExceptionalTermination) && !leafs.contains(nextNode)){
            GraphicsAlgorithm parentGA = getPictogramElementForBusinessObject(NodeUtil.getParent(nextNode)).getGraphicsAlgorithm();
            GraphicsAlgorithm nextGA = nextPE.getGraphicsAlgorithm();
            nextGA.setX(parentGA.getX());
            
            if(nextGA.getY() < parentGA.getY() + parentGA.getHeight() + OFFSET) {
               moveSubTreeVertical(nextNode, parentGA.getY() + parentGA.getHeight() + OFFSET - nextGA.getY());
               updateAllMethodRectHeights((ISEDMethodCall) nextNode.getCallStack()[0], nextGA, nextNode instanceof ISEDMethodReturn);
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
   
   private void mist(ISEDMethodCall mc, ISEDDebugNode node) throws DebugException {
      AreaContext areaContext = new AreaContext();
      ISEDDebugNode parent = NodeUtil.getParent(node);

      PictogramElement pe = getPictogramElementForBusinessObject(parent);
      GraphicsAlgorithm parentGA = pe.getGraphicsAlgorithm();

      int areaX = -1;
      int areaY = parentGA.getY() + parentGA.getHeight() + OFFSET;
      
      ISEDDebugNode previousSibling = ArrayUtil.getPrevious(NodeUtil.getChildren(parent, true), node);
      
      if (previousSibling != null) {
         int subTreeWidth = findMostRightXInSubtree(previousSibling);//findMostRightXInMethod(mc, previousSibling);
//            System.out.println("W: " + subTreeWidth);
         if (subTreeWidth > -1) {
            // Add right to the previous sibling directly under parent
            GraphicsAlgorithm gas = getPictogramElementForBusinessObject(previousSibling).getGraphicsAlgorithm();
            areaX = subTreeWidth + OFFSET;
            areaY = gas.getY();
         }
      }

      if(node instanceof ISEDExceptionalTermination && !ArrayUtil.isEmpty(parent.getCallStack()))
      {
         PictogramElement mcPE = getPictogramElementForBusinessObject(parent.getCallStack()[0], 0);
         GraphicsAlgorithm mcGA = mcPE.getGraphicsAlgorithm();

         areaY = mcGA.getY() + mcGA.getHeight() + OFFSET + parentGA.getHeight() / 2;
      }

      // If we dont have any previous sibling or we dont have a subtree at the previous sibling
      if(areaX == -1) {
         // Add directly under parent, but use x of most left pe in branch
         areaX = findMostLeftXOfBranchInParents(parent);
      }

      areaContext.setX(areaX);
      areaContext.setY(areaY);


      AddContext addContext = new AddContext(areaContext, node);
      addContext.setTargetContainer(getDiagram());
      // Execute add feature manually because getFeatureProvider().addIfPossible(addContext) changes the selection
      IAddFeature feature = getFeatureProvider().getAddFeature(addContext);
      if (feature != null && feature.canExecute(addContext)) {
         feature.execute(addContext);
      }
   }
}