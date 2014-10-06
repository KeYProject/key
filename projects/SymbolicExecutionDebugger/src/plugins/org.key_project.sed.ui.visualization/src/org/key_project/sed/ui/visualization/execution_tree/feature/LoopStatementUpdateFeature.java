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

import java.util.LinkedHashSet;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.IUpdateFeature;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.key_project.sed.core.model.ISEDBaseMethodReturn;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDLoopCondition;
import org.key_project.sed.core.model.ISEDLoopStatement;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.util.ISEDIterator;
import org.key_project.sed.core.util.NodeUtil;
import org.key_project.sed.core.util.SEDLoopPreorderIterator;
import org.key_project.sed.core.util.SEDMethodPreorderIterator;
import org.key_project.util.java.ArrayUtil;

/**
 * Implementation of {@link IUpdateFeature} for {@link ISEDLoopStatement}s.
 * @author Martin Hentschel
 */
public class LoopStatementUpdateFeature extends AbstractDebugNodeUpdateFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IUpdateFeature}.
    */   
   public LoopStatementUpdateFeature(IFeatureProvider fp) {
      super(fp);
   }
   
   /*
    * TODO
    */
//   protected Set<ISEDDebugNode> expandChildrenLeft(ISEDLoopStatement ls, int maxX, IProgressMonitor monitor) throws DebugException {
   protected Set<ISEDDebugNode> updateChildrenLeftAligned(ISEDDebugElement debugElement, IProgressMonitor monitor, int offset, int maxX)throws DebugException {
      if(!(debugElement instanceof ISEDLoopStatement))
         return null;
      
      ISEDLoopStatement ls = (ISEDLoopStatement) debugElement;
      
      Set<ISEDDebugNode> leafs = new LinkedHashSet<ISEDDebugNode>();
      SEDLoopPreorderIterator iter = new SEDLoopPreorderIterator(ls);

      while (iter.hasNext() && !monitor.isCanceled()) {
         ISEDDebugElement next = iter.next();
         
         // Ignore the bo, because either it is ISEDDebugTarget (the very first bo) which has no graphical representation
         // or its a parentnode which already has a graphical representation
         if(next == ls) {
            continue;
         }

         ISEDDebugNode nextNode = (ISEDDebugNode)next;
//         System.out.println("Node: " + nextNode);
         PictogramElement nextPE = getPictogramElementForBusinessObject(next);
         if (nextPE == null) {
            createGraphicalRepresentationForNode(nextNode, OFFSET, 0);
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
            if (ArrayUtil.isEmpty(NodeUtil.getChildren(nextNode)) && !leafs.contains(nextNode)) {
               leafs.add(nextNode);
            }
            else {
               ISEDDebugNode child = ArrayUtil.getFirst(NodeUtil.getChildren(nextNode));
//               System.out.println(child);
               PictogramElement childPE = getPictogramElementForBusinessObject(child);
               if(childPE != null && child instanceof ISEDLoopCondition && !leafs.contains(child) && iter.getIteration() != 1) {
//                  System.out.println("Iter: " + iter.getIteration() + ", C: " + child);
//                  System.out.println("Y: " + childPE.getGraphicsAlgorithm().getY());
                  childPE.getGraphicsAlgorithm().setX(findMostLeftXOfBranchAbove(child));
                  leafs.add(child);
               }
            }
         }
         else {
            nextPE.getGraphicsAlgorithm().setX(findMostLeftXOfBranchAbove(nextNode));
            
            ISEDDebugNode child = ArrayUtil.getFirst(NodeUtil.getChildren(nextNode));
            PictogramElement childPE = getPictogramElementForBusinessObject(child);
            if(childPE != null && child instanceof ISEDLoopCondition && !leafs.contains(child) && iter.getIteration() != 1) {
   //            System.out.println("Iter: " + iter.getIteration() + ", C: " + child);
   //            System.out.println("Y: " + childPE.getGraphicsAlgorithm().getY());
               childPE.getGraphicsAlgorithm().setX(findMostLeftXOfBranchAbove(child));
               leafs.add(child);
            }
         }
      }
//      System.out.println("LA: " + leafs.size());
      return leafs;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean canUpdateBusinessObject(Object businessObject) {
      return businessObject instanceof ISEDLoopStatement;
   }
}