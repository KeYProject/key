package org.key_project.sed.ui.visualization.execution_tree.feature;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.impl.RemoveContext;
import org.eclipse.graphiti.features.context.impl.UpdateContext;
import org.eclipse.graphiti.features.custom.AbstractCustomFeature;
import org.eclipse.graphiti.features.impl.DefaultRemoveFeature;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.algorithms.Polyline;
import org.eclipse.graphiti.mm.pictograms.AnchorContainer;
import org.eclipse.graphiti.mm.pictograms.Connection;
import org.eclipse.graphiti.mm.pictograms.ConnectionDecorator;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.eclipse.graphiti.services.IPeCreateService;
import org.eclipse.graphiti.util.ColorConstant;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDGroupable;
import org.key_project.sed.core.util.ISEDIterator;
import org.key_project.sed.core.util.NodeUtil;
import org.key_project.sed.core.util.SEDGroupPreorderIterator;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeStyleUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.java.ArrayUtil;

public abstract class AbstractDebugNodeCollapseFeature extends AbstractCustomFeature {
   
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link ICustomFeature}.
    */
   public AbstractDebugNodeCollapseFeature(IFeatureProvider fp) {
      super(fp);
   }
   
   /**
   * {@inheritDoc}
   */
   @Override
   public boolean canExecute(ICustomContext context) {
      boolean canExecute = false;
      PictogramElement[] pes = context.getPictogramElements();
      if (pes != null) {
         int i = 0;
         while (i < pes.length && !canExecute) {
            Object businessObject = getBusinessObjectForPictogramElement(pes[i]);
            canExecute = canExecuteBusinessObject(businessObject);
            i++;
         }
      }
      return canExecute;
   }
   
   /**
    * Checks if the give business object can be handled by this {@link ICustomFeature}.
    * @param businessObject The business object to check.
    * @return {@code true} can execute, {@code false} can not execute.
    */
   protected boolean canExecuteBusinessObject(Object businessObject) {
      return NodeUtil.canBeGrouped(businessObject);
   }
   
   @Override
   public void execute(ICustomContext context) {
      PictogramElement[] pes = context.getPictogramElements();
      
      if(pes != null)
      {
         ISEDGroupable groupStart = (ISEDGroupable) getBusinessObjectForPictogramElement(pes[0]); // TODO: Handle all supported business objects
         pes = getFeatureProvider().getAllPictogramElementsForBusinessObject(groupStart);
         
         try
         {
            UpdateContext uc = new UpdateContext(pes[1]);
            AbstractDebugNodeUpdateFeature uf = (AbstractDebugNodeUpdateFeature) getFeatureProvider().getUpdateFeature(uc);

            IProgressMonitor monitor = GraphitiUtil.getProgressMonitor(context);
            ColorConstant color;
            
            if(!groupStart.isCollapsed()) {
               SEDGroupPreorderIterator iter = new SEDGroupPreorderIterator(groupStart);
               color = iter.allBranchesFinished() ? new ColorConstant(102, 180, 0) : new ColorConstant(255, 102, 0);
               
               removeChildren(groupStart);
//               removeConnections(pes[1]);
               
               groupStart.setCollapsed(true);

               updateCollapse(groupStart, uf, monitor);
            }
            else {
               DefaultRemoveFeature drf = new DefaultRemoveFeature(getFeatureProvider());
               ISEDBranchCondition[] bcs = NodeUtil.getSortedBCs(groupStart);
               for(ISEDBranchCondition bc : bcs) {
                  PictogramElement bcPE = uf.getPictogramElementForBusinessObject(bc);
                  removeConnections(bcPE, drf);
                  drf.remove(new RemoveContext(bcPE));
               }

               removeConnections(pes[1], drf);
               
               GraphicsAlgorithm rectGA = pes[0].getGraphicsAlgorithm();
               GraphicsAlgorithm nodeGA = pes[1].getGraphicsAlgorithm();

               int mostLeftInParent = uf.findMostLeftXOfBranchInParents((ISEDDebugNode) groupStart);
               int mostLeftInSubtree = uf.findMostLeftXInSubtree((ISEDDebugNode) groupStart);
               int mostLeft = mostLeftInParent < mostLeftInSubtree ? mostLeftInParent : mostLeftInSubtree;
               nodeGA.setX(mostLeft < rectGA.getX() ? mostLeft : rectGA.getX());
//               nodeGA.setX(mostLeftInParent < rectGA.getX() ? mostLeftInParent + uf.METOFF : rectGA.getX() + uf.METOFF);
               
               groupStart.setCollapsed(false);
               
               uf.update(uc);

               for(ISEDBranchCondition bc : bcs) {
                  ISEDDebugNode groupEnd = bc.getChildren()[0];

                  PictogramElement groupEndPE = uf.getPictogramElementForBusinessObject(groupEnd);
                  PictogramElement parentPE = uf.getPictogramElementForBusinessObject(NodeUtil.getParent(groupEnd));
                  
                  createConnection((AnchorContainer)parentPE, (AnchorContainer)groupEndPE);
               }

//               uf.resizeRectsIfNeeded(groupStart, monitor);
//               
//               if(NodeUtil.getGroupStartNode((ISEDDebugNode) groupStart) != null) {
//                  shrinkRectHeights(groupStart, uf);
//               }
               
               color = new ColorConstant(102, 80, 180);
            }
            
            pes[0].getGraphicsAlgorithm().setForeground(manageColor(color));
         }
         catch (DebugException e) {
            LogUtil.getLogger().logError(e);
         }
      }
   }
   
   /**
    * TODO
    */
   protected void updateCollapse(ISEDGroupable groupStart, AbstractDebugNodeUpdateFeature uf, IProgressMonitor monitor) throws DebugException {
      GraphicsAlgorithm rectGA = uf.getPictogramElementForBusinessObject(groupStart, 0).getGraphicsAlgorithm();
      GraphicsAlgorithm nodeGA = uf.getPictogramElementForBusinessObject(groupStart).getGraphicsAlgorithm();
      
      ISEDBranchCondition[] bcs = NodeUtil.getSortedBCs(groupStart);

      int maxX = rectGA.getX();
      Set<ISEDDebugNode> leafs = new HashSet<ISEDDebugNode>();
      
      nodeGA.setX(rectGA.getX());

      if(bcs.length > 1) {
         int above = uf.findBiggestWidthInPartTreeAbove((ISEDDebugNode) groupStart);
         // if there is a bigger node above our rect set the x-position to it
         if(above > rectGA.getWidth()) {
            nodeGA.setX(nodeGA.getX() - (above - nodeGA.getWidth()) / 2);
         }
//         else
//            nodeGA.setX(maxX);
      }
//      else {
//         nodeGA.setX(rectGA.getX());
//      }
      
      for(ISEDBranchCondition bc : bcs)
      {
         uf.createGraphicalRepresentationForNode(bc, uf.OFFSET, maxX);
         
         PictogramElement bcPE = uf.getPictogramElementForBusinessObject(bc);
         GraphicsAlgorithm bcGA = bcPE.getGraphicsAlgorithm();

         ISEDDebugNode groupEnd = bc.getChildren()[0];
         
         PictogramElement groupEndPE = uf.getPictogramElementForBusinessObject(groupEnd);
         GraphicsAlgorithm groupEndGA = groupEndPE.getGraphicsAlgorithm();
         
         //TODO fraglich ob nötig -> maxX nur beim ersten nötig
         // if the BC is to far left move it to rect.x + METOFF (only matters is the most left BC)
         if(maxX == rectGA.getX() && bcGA.getX() < maxX + uf.METOFF) {
            bcGA.setX(maxX + uf.METOFF);
         }
         
         if(bcs.length == 1) {
            int newX = uf.findMostLeftXOfBranchInParents((ISEDDebugNode) groupStart);
            if(uf.findBiggestWidthInPartTreeAbove(groupEnd) < groupEndGA.getWidth()) {
               newX += uf.METOFF;
            }
            
            groupEndGA.setX(newX);
         }

         if(bcGA.getWidth() < groupEndGA.getWidth() && bcs.length == 1) {
            bcGA.setX(groupEndGA.getX() + (groupEndGA.getWidth() - bcGA.getWidth()) / 2);
//            mrGA.setX(mrGA.getX() - METOFF);
         }
         else {
//            int subtreeWidth = uf.computeSubTreeWidth((ISEDDebugNode)groupStart);
//            if(subtreeWidth < rectGA.getWidth()) {
               int hMove = bcGA.getX() - groupEndGA.getX() + (bcGA.getWidth() - groupEndGA.getWidth()) / 2;
               uf.moveSubTreeHorizontal(groupEnd, hMove, true, new SubProgressMonitor(monitor, 1));
               // TODO vll sparen wenn hMove < 0
               int mostLeft = uf.findMostLeftXInSubtree(bc);
               if(mostLeft < bcGA.getX()) {
                  int mostRightXInPrev = uf.findMostRightXInPreviousBranch(bc);
                  uf.moveSubTreeHorizontal(bc, mostRightXInPrev + uf.OFFSET - mostLeft, true, new SubProgressMonitor(monitor, 1));
//                  uf.moveSubTreeHorizontal(bc, bcGA.getX() - mostLeft, true, new SubProgressMonitor(monitor, 1));
               }
//            }
         }
         
         maxX = uf.findMostRightXInSubtree(bc) + uf.OFFSET;

         createConnection((AnchorContainer)bcPE, (AnchorContainer)groupEndPE);
         
         leafs.add((bcGA.getWidth() > groupEndGA.getWidth() ? bc : groupEnd));
      }

      uf.shrinkRectHeights(groupStart);
      uf.centerChildren(new HashSet<ISEDDebugNode>(leafs), new SubProgressMonitor(monitor, 1));
      uf.adjustSubtreeIfSmaller((ISEDDebugNode) groupStart, new SubProgressMonitor(monitor, 1));
      monitor.worked(1);
      
//      resizeRectsIfNeeded(mc, monitor);
      
      if(bcs.length == 1)
      {
         for(ISEDDebugNode leaf : leafs) {
            
            if(ArrayUtil.isEmpty(NodeUtil.getChildren(leaf))) {
               continue;
            }
            
            PictogramElement leafPE = uf.getPictogramElementForBusinessObject(leaf);
            GraphicsAlgorithm leafGA = leafPE.getGraphicsAlgorithm();
            
            ISEDDebugNode child = NodeUtil.getChildren(leaf)[0];
            GraphicsAlgorithm childGA = uf.getPictogramElementForBusinessObject(child).getGraphicsAlgorithm();

            int toMove = leafGA.getX() - childGA.getX() + (leafGA.getWidth() - childGA.getWidth()) / 2;
            uf.moveSubTreeHorizontal(child, toMove, true, monitor);
         }
//         uf.adjustRects((ISEDDebugNode) groupStart, new SubProgressMonitor(monitor, 1));
      }

      uf.adjustRects((ISEDDebugNode) groupStart, new SubProgressMonitor(monitor, 1));

//      int mostLeftXInGroup = uf.findMostLeftXInGroup((ISEDDebugNode) groupStart) - uf.METOFF;
//
//      if(mostLeftXInGroup > rectGA.getX() && NodeUtil.getGroupStartNode((ISEDDebugNode) groupStart) != null) {
//         rectGA.setX(mostLeftXInGroup);
//      }
//
//      rectGA.setWidth(uf.findMostRightXInGroup(groupStart, (ISEDDebugNode) groupStart) + uf.METOFF - rectGA.getX());
      
      // TODO maybe doch nur resize :?
      uf.resizeRectsIfNeeded(groupStart, monitor);

      uf.updateParents(uf.getPictogramElementForBusinessObject(groupStart), uf.OFFSET, new SubProgressMonitor(monitor, 1));
      
      /**
       * Adjust Space between the left/right side of the group
       */
      int subtreeWidth = uf.computeSubTreeWidth((ISEDDebugNode)groupStart);
      
      if(subtreeWidth < rectGA.getWidth()) {
         int mostRightXInPrev = uf.findMostRightXInPreviousBranch((ISEDDebugNode) groupStart);
         int mostLeftXInSubtree = uf.findMostLeftXInSubtree((ISEDDebugNode) groupStart);
         int mostLeftXAbove = uf.findMostLeftXOfBranchAbove((ISEDDebugNode) groupStart);
         int mostLeftX = mostLeftXAbove < mostLeftXInSubtree ? mostLeftXAbove : mostLeftXInSubtree; 
   //      int mostLeftX = findMostLeftXInMethod(mc);
   //      int biggestWidthAbove = findBiggestWidthInPartTreeAbove(mc);
   //      System.out.println(mostLeftXAbove < mostLeftXInSubtree);
   //      if(biggestWidthAbove < rectGA.getWidth() && computeSubTreeWidth(mc) < rectGA.getWidth()) {
         int toMove = 0;
         ISEDGroupable outerGroup = NodeUtil.getGroupStartNode((ISEDDebugNode) groupStart);
         
         if(outerGroup != null) {
            GraphicsAlgorithm outerGA = uf.getPictogramElementForBusinessObject(outerGroup, 0).getGraphicsAlgorithm();
            
            // Either no prev branch or its more left then the outer rect
            if(mostRightXInPrev == -1 || mostRightXInPrev + uf.OFFSET <= outerGA.getX()) {
               toMove = outerGA.getX() + uf.METOFF - mostLeftX;
            }
            else {
               toMove = mostRightXInPrev + uf.OFFSET - mostLeftX;
            }
         }
         else if(mostRightXInPrev > -1 && mostLeftX > mostRightXInPrev + uf.OFFSET) {
            toMove = mostRightXInPrev + uf.OFFSET - mostLeftX;
         }
         
   //      if(mostRightXInPrev > -1 && mostLeftX > mostRightXInPrev + uf.OFFSET) {
   //         toMove = mostRightXInPrev + uf.OFFSET - mostLeftX;
   //         System.out.println("feff");
   //      }
   //      else if(outerGroup != null) {
   ////       System.out.println(outerGroup + ",  GS: " + groupStart);
   //       GraphicsAlgorithm parentMC = uf.getPictogramElementForBusinessObject(outerGroup, 0).getGraphicsAlgorithm();
   //       toMove = parentMC.getX() + uf.METOFF - mostLeftX;
   ////       System.out.println("2M: " + toMove);
   //      }
      
   
         
   //      if(outerGroup != null) {
   ////         System.out.println(outerGroup + ",  GS: " + groupStart);
   //         GraphicsAlgorithm parentMC = uf.getPictogramElementForBusinessObject(outerGroup, 0).getGraphicsAlgorithm();
   //         toMove = parentMC.getX() + uf.METOFF - mostLeftX;
   ////         System.out.println("2M: " + toMove);
   //      }
   //
   //      if(mostRightXInPrev > -1 && mostLeftX > mostRightXInPrev + uf.OFFSET) {
   //         toMove = mostRightXInPrev + uf.OFFSET - mostLeftX;
   //      }
   
         if(toMove != 0) {
            uf.moveRightAndAbove((ISEDDebugNode) groupStart, toMove, monitor);
            uf.moveSubTreeHorizontal((ISEDDebugNode) groupStart, toMove, true, monitor);
         }
      }
      
      uf.resizeRectsIfNeeded(groupStart, monitor);
   }
   
   /**
    * Creates an Arrowconnection between the the {@link AnchorContainer} startAC and
    * the {@link AnchorContainer} endAC
    * @param AnchorContainer startAC The AnchorContainer where the connections starts
    * @param AnchorContainer endAC The AnchorContainer where the connectons ends
    */
   protected void createConnection(AnchorContainer startAC, AnchorContainer endAC) {
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
    * This function removes all children and connections inside the given group
    * It will remove the connections of the start- and endnodes but not the nodes itself
    * @param ISEDGroupable groupStart The start node of the Group
    * @throws DebugException
    */
   protected void removeChildren(ISEDGroupable groupStart) throws DebugException {
      DefaultRemoveFeature drf = new DefaultRemoveFeature(getFeatureProvider());
      ISEDIterator iter = new SEDGroupPreorderIterator(groupStart);
      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();
        
         if(next instanceof ISEDDebugNode)
         {
            ISEDDebugNode nextNode = (ISEDDebugNode) next;
            PictogramElement[] pes = getFeatureProvider().getAllPictogramElementsForBusinessObject(nextNode);
            
            if(pes == null || nextNode.getGroupStartCondition((ISEDDebugNode) groupStart) != null) {
                continue;
            }
            
            removeConnections((NodeUtil.canBeGrouped(nextNode) ? pes[1] : pes[0]), drf);
            
            if(nextNode != (ISEDDebugNode) groupStart) {
               drf.remove(new RemoveContext(pes[0]));
               
               if(NodeUtil.canBeGrouped(nextNode)) {
                  drf.remove(new RemoveContext(pes[1]));
               }
            }
         }
      }
   }

   /**
    * Gathers all outgoing connections of the PictogramElement and removes them
    * @param PictogramElement pe The PictogramElement whose connections should be removed
    * @param DefaultRemoveFeature drf The DefaultRemoveFeature
    */
   protected void removeConnections(PictogramElement pe, DefaultRemoveFeature drf) {
      List<Connection> cons = Graphiti.getPeService().getOutgoingConnections((AnchorContainer) pe);

      for(Connection con : cons)
         drf.remove(new RemoveContext(con));
   }
}
