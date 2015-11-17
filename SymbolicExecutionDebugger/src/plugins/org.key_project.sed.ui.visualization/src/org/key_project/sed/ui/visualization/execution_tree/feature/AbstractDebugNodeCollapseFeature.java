package org.key_project.sed.ui.visualization.execution_tree.feature;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.impl.RemoveContext;
import org.eclipse.graphiti.features.context.impl.UpdateContext;
import org.eclipse.graphiti.features.custom.AbstractCustomFeature;
import org.eclipse.graphiti.features.custom.ICustomFeature;
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
import org.key_project.sed.core.model.ISEBranchCondition;
import org.key_project.sed.core.model.ISEDebugElement;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEGroupable;
import org.key_project.sed.core.util.ISEIterator;
import org.key_project.sed.core.util.NodeUtil;
import org.key_project.sed.core.util.SEGroupPreorderIterator;
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
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void execute(ICustomContext context) {
      PictogramElement[] pes = context.getPictogramElements();
      
      if(pes != null)
      {
         ISEGroupable groupStart = (ISEGroupable) getBusinessObjectForPictogramElement(pes[0]);
         pes = getFeatureProvider().getAllPictogramElementsForBusinessObject(groupStart);
         
         try
         {
            UpdateContext uc = new UpdateContext(pes[1]);
            AbstractDebugNodeUpdateFeature uf = (AbstractDebugNodeUpdateFeature) getFeatureProvider().getUpdateFeature(uc);

            IProgressMonitor monitor = GraphitiUtil.getProgressMonitor(context);
            ColorConstant color;
            
            // if the group is expanded, collapse it
            if(!groupStart.isCollapsed()) {
               SEGroupPreorderIterator iter = new SEGroupPreorderIterator(groupStart);
               color = iter.allBranchesFinished() ? new ColorConstant(102, 180, 0) : new ColorConstant(255, 102, 0);
               
               removeChildren(groupStart);
               groupStart.setCollapsed(true);
               updateCollapse(groupStart, uf, monitor);
            }
            // if the group is collapsed, expand it
            else {
               // Remove the BranchConditions and their connections
               DefaultRemoveFeature drf = new DefaultRemoveFeature(getFeatureProvider());
               ISEBranchCondition[] bcs = NodeUtil.getSortedBCs(groupStart);
               
               for(ISEBranchCondition bc : bcs) {
                  PictogramElement bcPE = uf.getPictogramElementForBusinessObject(bc, true);
                  removeConnections(bcPE, drf);
                  drf.remove(new RemoveContext(bcPE));
               }

               removeConnections(pes[1], drf);
               
               GraphicsAlgorithm rectGA = pes[0].getGraphicsAlgorithm();
               GraphicsAlgorithm nodeGA = pes[1].getGraphicsAlgorithm();

               int mostLeftAbove = uf.findAbove((ISENode) groupStart, true, true);
               int mostLeftInSubtree = uf.findInSubtree((ISENode) groupStart, true, true);
               int mostLeft = mostLeftAbove < mostLeftInSubtree ? mostLeftAbove : mostLeftInSubtree;

               // set groupstart node and rect like updateChildrenLeft
               nodeGA.setX(mostLeft < rectGA.getX() ? mostLeft : rectGA.getX());
               rectGA.setX(nodeGA.getX());
               
               groupStart.setCollapsed(false);
               
               // Re-add the group nodes
               uf.update(uc);

               // Add connections to the endnodes of the group
               for(ISEBranchCondition bc : bcs) {
                  ISENode groupEnd = bc.getChildren()[0];

                  PictogramElement groupEndPE = uf.getPictogramElementForBusinessObject(groupEnd, true);
                  PictogramElement parentPE = uf.getPictogramElementForBusinessObject(NodeUtil.getParent(groupEnd), true);
                  
                  createConnection((AnchorContainer)parentPE, (AnchorContainer)groupEndPE);
               }

               // Reset the color to blue
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
    * Performs the collapse of the given {@link ISEGroupable}.
    * @param groupStart The group to collapse.
    * @param uf The {@link AbstractDebugNodeUpdateFeature} to use.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception.
    */
   private void updateCollapse(ISEGroupable groupStart, AbstractDebugNodeUpdateFeature uf, IProgressMonitor monitor) throws DebugException {
      GraphicsAlgorithm rectGA = uf.getPictogramElementForBusinessObject(groupStart, 0).getGraphicsAlgorithm();
      GraphicsAlgorithm nodeGA = uf.getPictogramElementForBusinessObject(groupStart, true).getGraphicsAlgorithm();
      
      ISEBranchCondition[] bcs = NodeUtil.getSortedBCs(groupStart);

      LinkedList<ISENode> leafs = new LinkedList<ISENode>();
      
      nodeGA.setX(rectGA.getX());

      if(bcs.length > 1) {
         int above = uf.findBiggestWidthInPartTreeAbove((ISENode) groupStart, true);
         // if there is a bigger node above our rect set the x-position to it
         if(above > rectGA.getWidth()) {
            nodeGA.setX(uf.findAbove((ISENode) groupStart, true, true));
         }
      }
      
      // Add the branchconditions to the diagram
      for(ISEBranchCondition bc : bcs)
      { 
         // second parameter never used (parent always != null when collapsing)
         uf.createGraphicalRepresentationForNode(bc, true, 0);
         
         PictogramElement bcPE = uf.getPictogramElementForBusinessObject(bc, true);
         GraphicsAlgorithm bcGA = bcPE.getGraphicsAlgorithm();

         ISENode groupEnd = bc.getChildren()[0];
         
         PictogramElement groupEndPE = uf.getPictogramElementForBusinessObject(groupEnd, true);
         GraphicsAlgorithm groupEndGA = groupEndPE.getGraphicsAlgorithm();
         
         // center the subtree below the new branchcondition
         int toMove = bcGA.getX() - groupEndGA.getX() + (bcGA.getWidth() - groupEndGA.getWidth()) / 2;
         uf.moveSubTreeHorizontal(groupEnd, true, toMove, true, new SubProgressMonitor(monitor, 1));

         int mostLeft = uf.findInSubtree(bc, true, false);
         if(mostLeft < bcGA.getX()) {
            int mostRightXInPrev = uf.findInSiblingBranch(bc, true, false);
            // if there is a prev branch and the subtree is bigger than the branchcondition
            // adjust the branch
            if(mostRightXInPrev != -1) {
               uf.moveSubTreeHorizontal(bc, true, mostRightXInPrev + uf.OFFSET - mostLeft, true, new SubProgressMonitor(monitor, 1));
            }
         }

         createConnection((AnchorContainer)bcPE, (AnchorContainer)groupEndPE);
         leafs.add((bcGA.getWidth() > groupEndGA.getWidth() ? bc : groupEnd));
      }

      uf.shrinkRectHeights(groupStart, true);
      uf.centerChildren(new HashSet<ISENode>(leafs), true, new SubProgressMonitor(monitor, 1));
      uf.adjustSubtreeIfSmaller((ISENode) groupStart, true, new SubProgressMonitor(monitor, 1));
      monitor.worked(1);

      // if the group has only one branch we need to adjust it manually
      if(bcs.length == 1)
      {
         ISENode leaf = leafs.get(0);
         ISENode child = ArrayUtil.getFirst(NodeUtil.getChildren(leaf));
         
         if(child != null) {
            GraphicsAlgorithm leafGA = uf.getPictogramElementForBusinessObject(leaf, true).getGraphicsAlgorithm();
            GraphicsAlgorithm childGA = uf.getPictogramElementForBusinessObject(child, true).getGraphicsAlgorithm();

            int toMove = leafGA.getX() - childGA.getX() + (leafGA.getWidth() - childGA.getWidth()) / 2;
            uf.moveSubTreeHorizontal(child, true, toMove, true, monitor);
            
            int mostLeft = uf.findInSubtree(leaf, true, true);
            int mostRightXInPrev = uf.findInSiblingBranch(leaf, true, false);
            // adjust the branch with respect to the prev branch
            if(mostRightXInPrev != -1) {
               toMove = mostRightXInPrev + uf.OFFSET - mostLeft;
               uf.moveRightAndAbove(leaf, true, toMove, monitor);
               uf.moveSubTreeHorizontal(leaf, true, toMove, true, new SubProgressMonitor(monitor, 1));
            }
         }
      }
      
      // if the group node overlaps the rect now, we have to reposition the rect
      if(rectGA.getX() > 0 && nodeGA.getX() < rectGA.getX() + uf.METOFF) {
         rectGA.setX(nodeGA.getX() - uf.METOFF);
      }

      uf.adjustRects((ISENode) groupStart, true, new SubProgressMonitor(monitor, 1));
      uf.updateParents(uf.getPictogramElementForBusinessObject(groupStart, true), new SubProgressMonitor(monitor, 1));
      
      /**
       * Adjust Space between the left/right side of the group
       */
      int mostRightXInPrev = uf.findInSiblingBranch((ISENode) groupStart, true, false);
      int mostLeftXInSubtree = uf.findInSubtree((ISENode) groupStart, true, true);
      int mostLeftXAbove = uf.findAbove((ISENode) groupStart, true, true);
      int mostLeftX = mostLeftXAbove < mostLeftXInSubtree ? mostLeftXAbove : mostLeftXInSubtree; 

      int toMove = 0;
      ISEGroupable outerGroup = NodeUtil.getGroupStartNode((ISENode) groupStart);
      
      if(outerGroup != null) {
         GraphicsAlgorithm outerGA = uf.getPictogramElementForBusinessObject(outerGroup, 0).getGraphicsAlgorithm();
         
         // Either no prev branch or its more left then the outer rect
         // Not needed?, no problems so far...
         if(mostRightXInPrev == -1 || mostRightXInPrev + uf.OFFSET <= outerGA.getX()) {
//               toMove = outerGA.getX() + uf.METOFF - mostLeftX;
         }
         else {
            toMove = mostRightXInPrev + uf.OFFSET - mostLeftX;
         }
      }
      else if(mostRightXInPrev > -1 && mostLeftX > mostRightXInPrev + uf.OFFSET) {
         toMove = mostRightXInPrev + uf.OFFSET - mostLeftX;
      }

      if(toMove != 0) {
         uf.moveRightAndAbove((ISENode) groupStart, true, toMove, monitor);
         uf.moveSubTreeHorizontal((ISENode) groupStart, true, toMove, true, monitor);
      }
      
      uf.resizeRectsIfNeeded(groupStart, true, monitor);
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
    * This function removes all children and connections inside the given group (methodbody).
    * @param ISEGroupable groupStart The start node of the group.
    * @throws DebugException Occured Exception.
    */
   protected void removeChildren(ISEGroupable groupStart) throws DebugException {
      DefaultRemoveFeature drf = new DefaultRemoveFeature(getFeatureProvider());
      ISEIterator iter = new SEGroupPreorderIterator(groupStart);
      while (iter.hasNext()) {
         ISEDebugElement next = iter.next();
        
         if(next instanceof ISENode)
         {
            ISENode nextNode = (ISENode) next;
            PictogramElement[] pes = getFeatureProvider().getAllPictogramElementsForBusinessObject(nextNode);
            
            if(pes == null || nextNode.getGroupStartCondition((ISENode) groupStart) != null) {
                continue;
            }
            
            // Remove the connections of the node 
            removeConnections((NodeUtil.canBeGrouped(nextNode) ? pes[1] : pes[0]), drf);
            
            // If its a node of the methodbody we can remove it
            if(nextNode != (ISENode) groupStart) {
               drf.remove(new RemoveContext(pes[0]));
               
               // If the node opens an other group we need to remove the rect too 
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
