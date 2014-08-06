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
import org.eclipse.graphiti.mm.algorithms.Polyline;
import org.eclipse.graphiti.mm.pictograms.AnchorContainer;
import org.eclipse.graphiti.mm.pictograms.Connection;
import org.eclipse.graphiti.mm.pictograms.ConnectionDecorator;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.platform.IPlatformImageConstants;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.eclipse.graphiti.services.IPeCreateService;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeStyleUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;

public class MethodCallCollapseFeature extends AbstractDebugNodeCollapseFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link ICustomFeature}.
    */
   public MethodCallCollapseFeature(IFeatureProvider fp) {
      super(fp);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean canExecuteBusinessObject(Object businessObject) {
      return businessObject instanceof ISEDMethodCall;
   }
   

   @Override
   public void execute(ICustomContext context) {
      PictogramElement[] pes = context.getPictogramElements();
      
      if(pes != null)
      {
         ISEDMethodCall mc = (ISEDMethodCall) getBusinessObjectForPictogramElement(pes[0]);
         pes = getFeatureProvider().getAllPictogramElementsForBusinessObject(mc);
         
         try
         {
            UpdateContext uc;
            MethodCallUpdateFeature uf;
            
            uc = new UpdateContext(pes[1]);
            uf = (MethodCallUpdateFeature) getFeatureProvider().getUpdateFeature(uc);
            
            ISEDBranchCondition[] bcs = uf.getSortedBCs(mc);
            
            GraphicsAlgorithm rectGA = pes[0].getGraphicsAlgorithm();
            GraphicsAlgorithm nodeGA = pes[1].getGraphicsAlgorithm();
            
            int OFFSET = getDiagram().getGridUnit() * 2;
            int height = 2 * (nodeGA.getHeight() + OFFSET);
            IProgressMonitor monitor = GraphitiUtil.getProgressMonitor(context);
            
            if(!mc.isCollapsed())
            {
               uf.removeChildren(mc, mc);
               uf.removeConnections(pes[1]);
               
               mc.setCollapsed(true);
               
               int diff = rectGA.getHeight() - height;

               Graphiti.getPeService().setPropertyValue(pes[0], "DIFF", Integer.toString(diff));
               uf.updateCollapsedRectHeight(mc, nodeGA, diff);

               int maxX = 0;
               boolean need2Move = true;

               nodeGA.setX(rectGA.getX());
//               Graphiti.getPeService().setPropertyValue(pes[1], "MOVE", Integer.toString(nodeGA.getX()));
               for(ISEDBranchCondition bc : bcs)
               {
//                  AreaContext areaContext = new AreaContext();
//                  areaContext.setX(maxX);
//                  areaContext.setY(rectGA.getY() + nodeGA.getHeight() / 2 + OFFSET);
//                  
//                  AddContext addContext = new AddContext(areaContext, bc);
//                  addContext.setTargetContainer(getDiagram());
//                  // Execute add feature manually because getFeatureProvider().addIfPossible(addContext) changes the selection
//                  IAddFeature feature = getFeatureProvider().getAddFeature(addContext);
//                  if (feature != null && feature.canExecute(addContext)) {
//                     feature.execute(addContext);
//                  }

                  uf.createGraphicalRepresentationForNode(bc, OFFSET, maxX);
                  
                  
                  PictogramElement bcPE = getFeatureProvider().getPictogramElementForBusinessObject(bc);
                  GraphicsAlgorithm bcGA = bcPE.getGraphicsAlgorithm();

                  ISEDMethodReturn mr = (ISEDMethodReturn) bc.getChildren()[0];
                  PictogramElement mrPE = getFeatureProvider().getPictogramElementForBusinessObject(mr);
                  GraphicsAlgorithm mrGA = mrPE.getGraphicsAlgorithm();
                  
//                     uf.updateChildren(pictogramElement, offsetBetweenPictogramElements, monitor)
                  
                  int widthDiff = bcGA.getX() + bcGA.getWidth() - mrGA.getX() - mrGA.getWidth();

                  if(bcGA.getWidth() < mrGA.getWidth())
                  {
                     bcGA.setX(mrGA.getX() + (mrGA.getWidth() - bcGA.getWidth()) / 2);
                     need2Move = false;
                  }
//                        if(widthDiff > 0)
//                           bcGA.setX(bcGA.getX() + bcGA.getWidth() + OFFSET);
//                        else
//                           bcGA.setX(mrGA.getX() + mrGA.getWidth() + OFFSET);
                  

                  maxX = uf.findMostRightXInSubtree(bc) + OFFSET;
                  
                  int hMove = 0;
                  
                  if(need2Move)
                  {
                     hMove = (bcGA.getX() - mrGA.getX() + widthDiff) / 2;
                     uf.moveSubTreeHorizontal(mr, hMove, new SubProgressMonitor(monitor, 1));
                  }

                  Graphiti.getPeService().setPropertyValue(mrPE, "MOVE", Integer.toString(hMove));
                  
                  createConnection((AnchorContainer)bcPE, (AnchorContainer)mrPE);
               }
               
               Set<ISEDDebugNode> leafs = new HashSet<ISEDDebugNode>();
               leafs.add(mc);
               uf.centerChildren(leafs, new SubProgressMonitor(monitor, 1));
               monitor.worked(1);
            }
            else
            {
               DefaultRemoveFeature drf = new DefaultRemoveFeature(getFeatureProvider());
               for(ISEDBranchCondition bc : bcs) {
                  PictogramElement pe = getFeatureProvider().getPictogramElementForBusinessObject(bc);
                  uf.removeConnections(pe, drf);
                  drf.remove(new RemoveContext(pe));
               }

               uf.removeConnections(pes[1], drf);
               
               mc.setCollapsed(false);
               
               rectGA.setHeight(nodeGA.getHeight() / 2);
               nodeGA.setX(rectGA.getX());
//               nodeGA.setX(Integer.parseInt(Graphiti.getPeService().getPropertyValue(pes[1], "X")));
               
               for(ISEDBranchCondition bc : bcs) {
                  ISEDMethodReturn mr = (ISEDMethodReturn) bc.getChildren()[0];
                  PictogramElement mrPE = getFeatureProvider().getPictogramElementForBusinessObject(mr);

                  uf.moveSubTreeHorizontal(mr, -Integer.parseInt(Graphiti.getPeService().getPropertyValue(mrPE, "MOVE")), new SubProgressMonitor(monitor, 1));
               }
               
               uf.updateCollapsedRectHeight(mc, nodeGA, -Integer.parseInt(Graphiti.getPeService().getPropertyValue(pes[0], "DIFF")));
               uf.updateChildren(pes[1], OFFSET, new SubProgressMonitor(monitor, 1));
               monitor.worked(1);
               
               for(ISEDBranchCondition bc : bcs) {
                   ISEDMethodReturn mr = (ISEDMethodReturn) uf.getChildren(bc)[0];
                   PictogramElement mrPE = getFeatureProvider().getPictogramElementForBusinessObject(mr);
                   PictogramElement parentPE = getFeatureProvider().getPictogramElementForBusinessObject(uf.getParent(mr));
                   
                   createConnection((AnchorContainer)parentPE, (AnchorContainer)mrPE);
                   uf.updateParents(mrPE, OFFSET, new SubProgressMonitor(monitor, 1));
                   monitor.worked(1);
                }
            }
            
//            mc.setCollapsed(!mc.isCollapsed());
         }
         catch (DebugException e) {
            LogUtil.getLogger().logError(e);
         }
      }
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
   public String getName() {
      return "Collapse/Expand Functionbody";
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getDescription() {
      return "Collapse/Expand the Functionbody";
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getImageId() {
      return IPlatformImageConstants.IMG_EDIT_COLLAPSE;
   }
}
