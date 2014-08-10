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
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.IReason;
import org.eclipse.graphiti.features.IUpdateFeature;
import org.eclipse.graphiti.features.context.IUpdateContext;
import org.eclipse.graphiti.features.context.impl.RemoveContext;
import org.eclipse.graphiti.features.impl.DefaultRemoveFeature;
import org.eclipse.graphiti.features.impl.Reason;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.algorithms.Rectangle;
import org.eclipse.graphiti.mm.pictograms.AnchorContainer;
import org.eclipse.graphiti.mm.pictograms.Connection;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.services.Graphiti;
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
import org.key_project.util.java.ArrayUtil;

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
   
   protected Set<ISEDDebugNode> updateSubTree(ISEDDebugNode businessObject) throws DebugException {
      Set<ISEDDebugNode> leafs = new LinkedHashSet<ISEDDebugNode>();
      ISEDIterator iter = new SEDPreorderIterator(businessObject);
      while (iter.hasNext()) {
         ISEDDebugNode next = (ISEDDebugNode) iter.next();
         PictogramElement nextPE = getPictogramElementForBusinessObject(next);
         
         if(nextPE != null)
         {
            boolean isLeaf = true;

            if(!ArrayUtil.isEmpty(NodeUtil.getChildren(next)))
            {
               for(ISEDDebugNode child : NodeUtil.getChildren(next))
               {
                  if(getPictogramElementForBusinessObject(child) != null) {
                     isLeaf = false;
                     break;
                  }
               }
            }
            
            if(isLeaf) {
               leafs.add(next);
            }
         }
      }
      return leafs;
   }
   
   protected void shrinkRectHeights(ISEDDebugNode mc) throws DebugException {
      GraphicsAlgorithm nodeGA = getPictogramElementForBusinessObject(mc).getGraphicsAlgorithm();
      GraphicsAlgorithm rectGA = getPictogramElementForBusinessObject(mc, 0).getGraphicsAlgorithm();
      
      int height = 2 * (nodeGA.getHeight() + OFFSET);
      int diff = rectGA.getHeight() - height;
      do
      {
         ISEDBranchCondition[] bcs = ((ISEDMethodCall) mc).getMethodReturnConditions();
         

         rectGA.setHeight(rectGA.getHeight() - diff);

         for(int i = 0; i < bcs.length; i++) {
            ISEDDebugNode mr = bcs[i].getChildren()[0];
            PictogramElement mrPE = getPictogramElementForBusinessObject(mr);
                             
            if(mrPE != null) {
               moveSubTreeBetweenMRVertical(mr, mr, -diff);
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
//         }
         mc = !ArrayUtil.isEmpty(mc.getCallStack()) ? mc.getCallStack()[0] : null;
         if(mc != null) {
            rectGA = getPictogramElementForBusinessObject(mc, 0).getGraphicsAlgorithm();
            int deepestY = findDeepestYInMethod((ISEDMethodCall) mc);
//            PictogramElement deepestPE = findDeepestYInMethod((ISEDMethodCall) mc);
//            GraphicsAlgorithm deepestGA = deepestPE.getGraphicsAlgorithm();

            if(deepestY > rectGA.getY() + rectGA.getHeight() - diff) {
               diff = rectGA.getY() + rectGA.getHeight() - deepestY - OFFSET - nodeGA.getHeight() / 2;
            }   
         }
      } while(mc != null);
   }
   
   private int findDeepestYInMethod(ISEDMethodCall mc) throws DebugException {
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
   
//   private PictogramElement findDeepestYInMethod(ISEDMethodCall mc) throws DebugException {
//      int deepestY = 0;
//      PictogramElement deepestPE = null;
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
//            if(nextNode instanceof ISEDMethodReturn)
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
//                  System.out.println(nextNode);
//                  deepestY = ga.getY() + ga.getHeight();
//                  deepestPE = pe;
//               }
//            }
//         }
//      }
//
//      return deepestPE;
//   }
   
   /**
    * Moves all nodes in the sub tree between the given {@link ISEDMethodReturn} and
    * the next {@link ISEDMethodReturn} or {@link ISEDTermination} vertical by the given distance.
    * @param mr The {@link ISEDDebugNode} to start with.
    * @param node The {@link ISEDDebugNode} to start moving.
    * @param distance The distance to move in x direction.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception
    */
   protected void moveSubTreeBetweenMRVertical(ISEDDebugNode mr, ISEDDebugNode node, int distance) throws DebugException {
      
      if(node == null || node instanceof ISEDMethodReturn && !node.equals(mr))
         return;
      
      PictogramElement pe = getPictogramElementForBusinessObject(node);
      if (pe != null) {
//         System.out.println(node);
         pe.getGraphicsAlgorithm().setY(pe.getGraphicsAlgorithm().getY() + distance);
      }
      
      for(ISEDDebugNode child : NodeUtil.getChildren(node)) {
         moveSubTreeBetweenMRVertical(mr, child, distance);
      }
   }
   
   /**
    * This function removes all children and connections of the given node, until
    * there are no more children or {@link ISEDMethodReturn} is reached and returns
    * all found MethodReturns.
    * @param ISEDDebugNode node The current node
    * @return Set<ISEDDebugNode> methodCloses Contains all MethodReturns
    * @throws DebugException
    */
   protected void removeChildren(ISEDMethodCall node, ISEDMethodCall mc) throws DebugException {
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

//            if(!(nextNode instanceof ISEDMethodReturn) || nextNode.getCallStack()[0] != mc)
//               removeChildren(child, mc);
            
            for(PictogramElement pe : pes)
            {
               if(!(nextNode instanceof ISEDMethodCall)) {
                  removeConnections(pe, drf);
               }
               drf.remove(new RemoveContext(pe));
            }
         }
      }
//      
//      ISEDDebugNode[] children = NodeUtil.getChildren(node);
//      
//      if(children.length == 0)
//         return;
//      
//      DefaultRemoveFeature drf = new DefaultRemoveFeature(getFeatureProvider());
//      
//      for(ISEDDebugNode child : children)
//      {
//         PictogramElement[] pes = getFeatureProvider().getAllPictogramElementsForBusinessObject(child);
//         
//         if(pes == null || child instanceof ISEDMethodReturn && child.getCallStack()[0] == mc ||
//              !(child instanceof ISEDBranchCondition) && ArrayUtil.isEmpty(child.getCallStack())) {
//            continue;
//         }
//
//         if(!(child instanceof ISEDMethodReturn) || child.getCallStack()[0] != mc)
//            removeChildren(child, mc);
//         
//         for(PictogramElement pe : pes)
//         {
//            if(!(child instanceof ISEDMethodCall)) {
//               removeConnections(pe, drf);
//            }
//            drf.remove(new RemoveContext(pe));
//         }
//      }
   }
   
   protected void removeConnections(PictogramElement pe) {
      removeConnections(pe, new DefaultRemoveFeature(getFeatureProvider()));
   }

   protected void removeConnections(PictogramElement pe, DefaultRemoveFeature drf) {
      List<Connection> cons = Graphiti.getPeService().getOutgoingConnections((AnchorContainer) pe);
   
      for(Connection con : cons)
         drf.remove(new RemoveContext(con));
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean canUpdateBusinessObject(Object businessObject) {
      return businessObject instanceof ISEDMethodCall;
   }
}