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
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.core.util.ISEDIterator;
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

            if(!ArrayUtil.isEmpty(getChildren(next)))
            {
               for(ISEDDebugNode child : getChildren(next))
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

   protected void updateCollapsedRectHeight(ISEDDebugNode mc, GraphicsAlgorithm ga, int diff) throws DebugException {
      do
      {
         PictogramElement mcPE = getPictogramElementForBusinessObject(mc, 0);
         GraphicsAlgorithm mcGA = mcPE.getGraphicsAlgorithm();

         ISEDBranchCondition[] bcs = ((ISEDMethodCall) mc).getMethodReturnConditions();

         mcGA.setHeight(mcGA.getHeight() - diff);
         
         for(int i = 0; i < bcs.length; i++) {
            ISEDDebugNode mr = bcs[i].getChildren()[0];
            PictogramElement mrPE = getPictogramElementForBusinessObject(mr);
            
            if(mrPE != null) {
//               mrPE.getGraphicsAlgorithm().setY(mrPE.getGraphicsAlgorithm().getY() - diff);
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

         mc = !ArrayUtil.isEmpty(mc.getCallStack()) ? mc.getCallStack()[0] : null;
         if(mc != null) {
            mcPE = getPictogramElementForBusinessObject(mc, 0);
            mcGA = mcPE.getGraphicsAlgorithm();
            if(diff > 0)
            {
               if(findDeepestYInMethod(mc, mc, 0) > mcGA.getY() + mcGA.getHeight() - diff) {
                  mc = null;
               }   
            }
            else
            {
               if(findDeepestYInMethod(mc, mc, 0) < mcGA.getY() + mcGA.getHeight() + diff) {
                  mc = null;
               }
            }
         }
      } while(mc != null);
   }
   
   private int findDeepestYInMethod(ISEDDebugNode mc, ISEDDebugNode node, int deepestY) throws DebugException {
      
      if(node == null || !(node instanceof ISEDBranchCondition) && ArrayUtil.isEmpty(node.getCallStack()) && !node.equals(mc)) {
         return deepestY;
      }
      
      if(node instanceof ISEDMethodReturn)
      {
         if(node.getCallStack()[0].equals(mc)) {
            return deepestY;
         }
      }
      
      PictogramElement pe = getPictogramElementForBusinessObject(node);
      if (pe != null) {
         if (pe.getGraphicsAlgorithm().getY() > deepestY) {
            deepestY = pe.getGraphicsAlgorithm().getY();
         }
      }
      
      for(ISEDDebugNode child : getChildren(node)) {
         deepestY = findDeepestYInMethod(mc, child, deepestY);
      }

      return deepestY;
   }
   
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
         pe.getGraphicsAlgorithm().setY(pe.getGraphicsAlgorithm().getY() + distance);
      }
      
      for(ISEDDebugNode child : getChildren(node)) {
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
   protected void removeChildren(ISEDDebugNode node, ISEDMethodCall mc) throws DebugException {
      ISEDDebugNode[] children = getChildren(node);
      
      if(children.length == 0)
         return;
      
      DefaultRemoveFeature drf = new DefaultRemoveFeature(getFeatureProvider());
      
      for(ISEDDebugNode child : children)
      {
         PictogramElement[] pes = getFeatureProvider().getAllPictogramElementsForBusinessObject(child);
         
         if(pes == null || child instanceof ISEDMethodReturn && child.getCallStack()[0] == mc ||
              !(child instanceof ISEDBranchCondition) && ArrayUtil.isEmpty(child.getCallStack())) {
            continue;
         }

         if(!(child instanceof ISEDMethodReturn) || child.getCallStack()[0] != mc)
            removeChildren(child, mc);
         
         for(PictogramElement pe : pes)
         {
            if(!(child instanceof ISEDMethodCall)) {
               removeConnections(pe, drf);
            }
            drf.remove(new RemoveContext(pe));
         }
      }
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