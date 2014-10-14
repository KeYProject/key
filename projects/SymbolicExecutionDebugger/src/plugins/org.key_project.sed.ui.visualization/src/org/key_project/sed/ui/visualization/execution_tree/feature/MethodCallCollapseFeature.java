package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.core.runtime.IProgressMonitor;
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
import org.eclipse.graphiti.util.ColorConstant;
import org.key_project.sed.core.model.ISEDBaseMethodReturn;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.util.ISEDIterator;
import org.key_project.sed.core.util.NodeUtil;
import org.key_project.sed.core.util.SEDMethodPreorderIterator;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeStyleUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.java.ArrayUtil;

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
         ISEDMethodCall mc = (ISEDMethodCall) getBusinessObjectForPictogramElement(pes[0]); // TODO: Handle all supported business objects
         pes = getFeatureProvider().getAllPictogramElementsForBusinessObject(mc);
         
         try
         {
            UpdateContext uc = new UpdateContext(pes[1]);
            MethodCallUpdateFeature uf = (MethodCallUpdateFeature) getFeatureProvider().getUpdateFeature(uc);

            IProgressMonitor monitor = GraphitiUtil.getProgressMonitor(context);
            ColorConstant color;
            
            if(!mc.isCollapsed()) {
               SEDMethodPreorderIterator iter = new SEDMethodPreorderIterator(mc);
               color = iter.allBranchesFinished() ? new ColorConstant(102, 180, 0) : new ColorConstant(255, 102, 0);
               
               removeChildren(mc);
               removeConnections(pes[1]);
               
               mc.setCollapsed(true);

               uf.updateCollapse(mc, monitor);
            }
            else {
               DefaultRemoveFeature drf = new DefaultRemoveFeature(getFeatureProvider());
               ISEDBranchCondition[] bcs = NodeUtil.getSortedBCs(mc);
               for(ISEDBranchCondition bc : bcs) {
                  PictogramElement bcPE = getFeatureProvider().getPictogramElementForBusinessObject(bc);
                  removeConnections(bcPE, drf);
                  drf.remove(new RemoveContext(bcPE));
               }

               removeConnections(pes[1], drf);
               
               GraphicsAlgorithm rectGA = pes[0].getGraphicsAlgorithm();
               GraphicsAlgorithm nodeGA = pes[1].getGraphicsAlgorithm();

               int mostLeftInParent = uf.findMostLeftXOfBranchInParents(mc);
               
               nodeGA.setX(mostLeftInParent < rectGA.getX() ? mostLeftInParent + uf.METOFF : rectGA.getX() + uf.METOFF);
               
               mc.setCollapsed(false);
               
               uf.update(uc);

               for(ISEDBranchCondition bc : bcs) {
                  ISEDBaseMethodReturn mr = (ISEDBaseMethodReturn) bc.getChildren()[0];
                  PictogramElement mrPE = getFeatureProvider().getPictogramElementForBusinessObject(mr);
                  PictogramElement parentPE = getFeatureProvider().getPictogramElementForBusinessObject(NodeUtil.getParent(mr));
                  
                  createConnection((AnchorContainer)parentPE, (AnchorContainer)mrPE);
               }

               uf.resizeRectsIfNeeded(mc, monitor);

               if(!ArrayUtil.isEmpty(mc.getCallStack())) {
                  shrinkRectHeights(mc, uf);
               }
               
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
    * {@inheritDoc}
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
    * {@inheritDoc}
    */
   @Override
   protected void removeChildren(ISEDDebugNode node)
         throws DebugException {
      DefaultRemoveFeature drf = new DefaultRemoveFeature(getFeatureProvider());
      ISEDIterator iter = new SEDMethodPreorderIterator((ISEDMethodCall) node);
      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();
         
         if(next.equals(node)) {
            continue;
         }
         
         if(next instanceof ISEDDebugNode)
         {
            ISEDDebugNode nextNode = (ISEDDebugNode) next;

            PictogramElement[] pes = getFeatureProvider().getAllPictogramElementsForBusinessObject(nextNode);
            
            if(pes == null || nextNode instanceof ISEDBaseMethodReturn && nextNode.getCallStack()[0] == node ||
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
