package org.key_project.sed.ui.visualization.execution_tree.feature;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.impl.RemoveContext;
import org.eclipse.graphiti.features.context.impl.UpdateContext;
import org.eclipse.graphiti.features.impl.DefaultRemoveFeature;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.pictograms.AnchorContainer;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.platform.IPlatformImageConstants;
import org.eclipse.graphiti.util.ColorConstant;
import org.key_project.sed.core.model.ISEDBaseMethodReturn;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDLoopStatement;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.util.ISEDIterator;
import org.key_project.sed.core.util.NodeUtil;
import org.key_project.sed.core.util.SEDMethodPreorderIterator;
import org.key_project.sed.core.util.SEDPreorderIterator;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.java.ArrayUtil;

public class LoopStatementCollapseFeature extends AbstractDebugNodeCollapseFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link ICustomFeature}.
    */
   public LoopStatementCollapseFeature(IFeatureProvider fp) {
      super(fp);
   }

   @Override
   public void execute(ICustomContext context) {
      PictogramElement[] pes = context.getPictogramElements();
      
      if(pes != null)
      {
         ISEDLoopStatement ls = (ISEDLoopStatement) getBusinessObjectForPictogramElement(pes[0]);
         pes = getFeatureProvider().getAllPictogramElementsForBusinessObject(ls);
         
         UpdateContext uc = new UpdateContext(pes[0]);
         LoopStatementUpdateFeature uf = (LoopStatementUpdateFeature) getFeatureProvider().getUpdateFeature(uc);

      }
   }
   
//   protected void updateCollapse(ISEDLoopStatement ls, IProgressMonitor monitor) throws DebugException {
//      GraphicsAlgorithm rectGA = getPictogramElementForBusinessObject(ls, 0).getGraphicsAlgorithm();
//      GraphicsAlgorithm nodeGA = getPictogramElementForBusinessObject(ls).getGraphicsAlgorithm();
//
//      removeChildren(ls, ls);
//      removeConnections(getPictogramElementForBusinessObject(ls));
//
//      int maxX = rectGA.getX();
//      Set<ISEDDebugNode> leafs = new HashSet<ISEDDebugNode>();
//
//      if(bcs.length > 1) {
//         int above = findBiggestWidthInPartTreeAbove(ls);
//         if(above > rectGA.getWidth()) {
////            leafs.add(mc);
//            nodeGA.setX(nodeGA.getX() - (above - nodeGA.getWidth()) / 2);
//         }
//         else
//            nodeGA.setX(maxX);
////         leafs.add(mc);
////         nodeGA.setX(findMostLeftXInMethod(node));
//      }
//      else {
////         moveRightAndAbove(mc, maxX - nodeGA.getX(), monitor);
//         nodeGA.setX(rectGA.getX());
//      }
//      
//      boolean recenterMR = false;
//      for(ISEDBranchCondition bc : bcs)
//      {
//         createGraphicalRepresentationForNode(bc, OFFSET, maxX);
//         
//         PictogramElement bcPE = getFeatureProvider().getPictogramElementForBusinessObject(bc);
//         GraphicsAlgorithm bcGA = bcPE.getGraphicsAlgorithm();
//
//         ISEDBaseMethodReturn mr = (ISEDBaseMethodReturn) bc.getChildren()[0];
//         PictogramElement mrPE = getFeatureProvider().getPictogramElementForBusinessObject(mr);
//         GraphicsAlgorithm mrGA = mrPE.getGraphicsAlgorithm();
//         
//         if(maxX == rectGA.getX() && bcGA.getX() < maxX + METOFF) {
//            bcGA.setX(maxX + METOFF);
//         }
//         
//         if(bcs.length == 1) {
//            int newX = findMostLeftXOfBranchInParents(ls);
//            if(findBiggestWidthInPartTreeAbove(mr) < mrGA.getWidth()) {
//               newX += METOFF;
//            }
//            
//            mrGA.setX(newX);
//         }
//
//         if(bcGA.getWidth() < mrGA.getWidth() && bcs.length == 1) {
//            bcGA.setX(mrGA.getX() + (mrGA.getWidth() - bcGA.getWidth()) / 2);
////            mrGA.setX(mrGA.getX() - METOFF);
//         }
//         else {
//            if(!hasBiggerChild(mr, mrGA.getWidth()) || recenterMR) {
//               int hMove = bcGA.getX() - mrGA.getX() + (bcGA.getWidth() - mrGA.getWidth()) / 2;
//   //            System.out.println(hMove);
//               moveSubTreeHorizontal(mr, hMove, new SubProgressMonitor(monitor, 1));
//               
//               int mostLeft = findMostLeftXInSubtree(bc);
//               if(mostLeft < bcGA.getX()) {
//                  moveSubTreeHorizontal(bc, bcGA.getX() - mostLeft, new SubProgressMonitor(monitor, 1));
//   //               System.out.println(bc);
//               }
//               
//               recenterMR = true;
//            }
////            leafs.add((bcGA.getWidth() > mrGA.getWidth() ? bc : mr));
//         }
//         
//         maxX = findMostRightXInSubtree(bc) + OFFSET;
//
//         createConnection((AnchorContainer)bcPE, (AnchorContainer)mrPE);
//         
//         leafs.add((bcGA.getWidth() > mrGA.getWidth() ? bc : mr));
//         
////         if(bcs.length == 1)
////         {
//////            System.out.println(findMostLeftXOfBranchInParents(NodeUtil.getParent(mc)) + " -> " + mrGA.getX());
//////            if(findMostLeftXOfBranchInParents(NodeUtil.getParent(mc)) > mrGA.getX()) {
//////               mrGA.setX(mrGA.getX() - METOFF);
//////            }
//////            if(findBiggestWidthInPartTreeAbove(mr) > mrGA.getWidth()) {
//////               mrGA.setX(mrGA.getX() - METOFF);
//////            }
//////            if(findBiggestWidthInPartTreeAbove(mr) < mrGA.getWidth()) {
//////               nodeGA.setX(rectGA.getX() + METOFF);
////               leafs.add((bcGA.getWidth() > mrGA.getWidth() ? bc : mr));
//////            }
////         }
//      }
//
//      shrinkRectHeights(ls);
//      centerChildren(ls, new HashSet<ISEDDebugNode>(leafs), new SubProgressMonitor(monitor, 1));
//      monitor.worked(1);
//      
////      resizeRectsIfNeeded(mc, monitor);
//      
//      if(bcs.length == 1)
//      {
//         for(ISEDDebugNode leaf : leafs) {
//            
//            if(ArrayUtil.isEmpty(NodeUtil.getChildren(leaf))) {
//               continue;
//            }
//            
//            PictogramElement leafPE = getFeatureProvider().getPictogramElementForBusinessObject(leaf);
//            GraphicsAlgorithm leafGA = leafPE.getGraphicsAlgorithm();
//            
//            ISEDDebugNode child = NodeUtil.getChildren(leaf)[0];
//            GraphicsAlgorithm childGA = getPictogramElementForBusinessObject(child).getGraphicsAlgorithm();
//            GraphicsAlgorithm parentGA = getPictogramElementForBusinessObject(NodeUtil.getParent(leaf)).getGraphicsAlgorithm();
//            
//            int toMove = leafGA.getX() - childGA.getX() + (leafGA.getWidth() - childGA.getWidth()) / 2;
//            moveSubTreeHorizontal(child, toMove, monitor);
//            System.out.println(leaf);
//         }
//      }
//      
//      
////      resizeRectsIfNeeded(mc, monitor);
////
////      updateParents(getPictogramElementForBusinessObject(mc), OFFSET, new SubProgressMonitor(monitor, 1));
////      
//      resizeRectsIfNeeded(ls, monitor);
//   }

   @Override
   protected void removeChildren(ISEDDebugNode node)
         throws DebugException {
      DefaultRemoveFeature drf = new DefaultRemoveFeature(getFeatureProvider());
      ISEDIterator iter = new SEDPreorderIterator(node);
      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();
         
         if(next.equals(node)) {
            continue;
         }
         
         if(next instanceof ISEDDebugNode)
         {
            ISEDDebugNode nextNode = (ISEDDebugNode) next;
            PictogramElement pe = getFeatureProvider().getPictogramElementForBusinessObject(nextNode);
            
            if(pe == null) {
               continue;
            }
            
            if(!(nextNode instanceof ISEDMethodCall)) {
               removeConnections(pe, drf);
            }
            drf.remove(new RemoveContext(pe));
         }
      }
      
   }

   @Override
   protected boolean canExecuteBusinessObject(Object businessObject) {
      return businessObject instanceof ISEDLoopStatement;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return "Collapse/Expand Loop";
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getDescription() {
      return "Collapse/Expand the Loop";
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getImageId() {
      return IPlatformImageConstants.IMG_EDIT_COLLAPSE;
   }
}
