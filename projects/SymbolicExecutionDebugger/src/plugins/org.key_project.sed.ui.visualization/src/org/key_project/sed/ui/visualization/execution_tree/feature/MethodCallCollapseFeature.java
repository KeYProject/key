package org.key_project.sed.ui.visualization.execution_tree.feature;

import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.impl.AddContext;
import org.eclipse.graphiti.features.context.impl.AreaContext;
import org.eclipse.graphiti.features.context.impl.RemoveContext;
import org.eclipse.graphiti.features.context.impl.UpdateContext;
import org.eclipse.graphiti.features.impl.DefaultRemoveFeature;
import org.eclipse.graphiti.features.impl.Reason;
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
import org.key_project.sed.core.model.memory.SEDMemoryBranchStatement;
import org.key_project.sed.core.model.memory.SEDMemoryMethodReturn;
import org.key_project.sed.core.model.memory.SEDMemoryStatement;
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
            ISEDBranchCondition[] bcs = mc.getMethodReturnConditions();
            
            GraphicsAlgorithm rectGA = pes[0].getGraphicsAlgorithm();
            GraphicsAlgorithm nodeGA = pes[1].getGraphicsAlgorithm();
            
            int OFFSET = getDiagram().getGridUnit() * 2;
            int height = 2 * (nodeGA.getHeight() + OFFSET);
            
            if(!mc.isCollapsed())
            {
               mc.setCollapsed(!mc.isCollapsed());
               removeChildren(mc, mc);
               removeConnections(pes[1]);
               
               int methodHeight = Integer.parseInt(Graphiti.getPeService().getPropertyValue(pes[0], "height"));
               int diff = methodHeight - height;

//               System.out.println("MH: " + methodHeight + ", H: " + height);
//               if(methodHeight > height){
                  rectGA.setHeight(height);
                  Graphiti.getPeService().setPropertyValue(pes[0], "height", Integer.toString(height));
//               }
                  
               UpdateContext uc;
               AbstractDebugNodeUpdateFeature uf;
               
               for(ISEDBranchCondition bc : bcs)
               {
                  AreaContext areaContext = new AreaContext();
                  areaContext.setX(0);
                  areaContext.setY(rectGA.getY() + nodeGA.getHeight() / 2 + OFFSET);
                  
                  AddContext addContext = new AddContext(areaContext, bc);
                  addContext.setTargetContainer(getDiagram());
                  // Execute add feature manually because getFeatureProvider().addIfPossible(addContext) changes the selection
                  IAddFeature feature = getFeatureProvider().getAddFeature(addContext);
                  if (feature != null && feature.canExecute(addContext)) {
                     feature.execute(addContext);
                  }
                  
                  PictogramElement bcPE = getFeatureProvider().getPictogramElementForBusinessObject(bc);

                  for(ISEDDebugNode node : bc.getChildren()) {
                     ISEDMethodReturn mr = (ISEDMethodReturn) node;
                     PictogramElement mrPE = getFeatureProvider().getPictogramElementForBusinessObject(mr);
                     GraphicsAlgorithm mrGA = mrPE.getGraphicsAlgorithm();
                     
                     uc = new UpdateContext(mrPE);
                     uf = (AbstractDebugNodeUpdateFeature) getFeatureProvider().getUpdateFeature(uc);
                     uf.moveSubTreeVertical(mr, -diff);
                     
//                     mrGA.setY(mrGA.getY() - diff);
                     createConnection((AnchorContainer)bcPE, (AnchorContainer)mrPE);
                  }
               }
               
//               IProgressMonitor monitor = GraphitiUtil.getProgressMonitor(context);

               uc = new UpdateContext(pes[1]);
//               uf = (AbstractDebugNodeUpdateFeature) getFeatureProvider().getUpdateFeature(uc);
//               uf.centerChildren(new HashSet<ISEDDebugNode>(Arrays.asList(mc.getMethodReturnConditions())), new SubProgressMonitor(monitor, 1));
               MethodCallUpdateFeature mcuf = (MethodCallUpdateFeature) getFeatureProvider().getUpdateFeature(uc);
               mcuf.centerCollapsedMethod(mc.getMethodReturnConditions());
            }
            else
            {
               mc.setCollapsed(!mc.isCollapsed());
               DefaultRemoveFeature drf = new DefaultRemoveFeature(getFeatureProvider());
               for(ISEDBranchCondition bc : bcs) {
                  PictogramElement pe = getFeatureProvider().getPictogramElementForBusinessObject(bc);
                  removeConnections(pe, drf);
                  drf.remove(new RemoveContext(pe));
               }

               removeConnections(pes[1], drf);
               
               rectGA.setHeight(nodeGA.getHeight() / 2);
               Graphiti.getPeService().setPropertyValue(pes[0], "height", Integer.toString(nodeGA.getHeight() / 2));
               
               UpdateContext uc = new UpdateContext(pes[1]);
               AbstractDebugNodeUpdateFeature feature = (AbstractDebugNodeUpdateFeature) getFeatureProvider().getUpdateFeature(uc);
               feature.update(uc);
               
               rectGA.setHeight(rectGA.getHeight() + nodeGA.getHeight() + OFFSET);
               Graphiti.getPeService().setPropertyValue(pes[0], "height", Integer.toString(rectGA.getHeight()));
               
               for(ISEDBranchCondition bc : bcs) {
                  for(ISEDDebugNode node : bc.getChildren()) {
                     ISEDMethodReturn mr = (ISEDMethodReturn) node;
                     PictogramElement mrPE = getFeatureProvider().getPictogramElementForBusinessObject(mr);
                     PictogramElement parentPE = getFeatureProvider().getPictogramElementForBusinessObject(mr.getParent());
                     GraphicsAlgorithm mrGA = mrPE.getGraphicsAlgorithm();
                     
                     uc = new UpdateContext(mrPE);
                     feature = (AbstractDebugNodeUpdateFeature) getFeatureProvider().getUpdateFeature(uc);
                     feature.moveSubTreeVertical(mr, rectGA.getY() + rectGA.getHeight() - mrGA.getY() - mrGA.getHeight() / 2);
                     
//                     mrGA.setY(rectGA.getY() + rectGA.getHeight() - mrGA.getHeight() / 2);
                     createConnection((AnchorContainer)parentPE, (AnchorContainer)mrPE);
                  }
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
    * This function removes all children and connections of the given node, until
    * there are no more children or {@link ISEDMethodReturn} is reached and returns
    * all found MethodReturns.
    * @param ISEDDebugNode node The current node
    * @return Set<ISEDDebugNode> methodCloses Contains all MethodReturns
    * @throws DebugException
    */
   private void removeChildren(ISEDDebugNode node, ISEDMethodCall mc) throws DebugException {
      ISEDDebugNode[] children = node.getChildren();
      
      if(children.length == 0)
         return;
      
      DefaultRemoveFeature drf = new DefaultRemoveFeature(getFeatureProvider());
      
      for(ISEDDebugNode child : children)
      {
         PictogramElement[] pes = getFeatureProvider().getAllPictogramElementsForBusinessObject(child);
         
         if(pes == null || child instanceof ISEDMethodReturn && child.getCallStack()[0] == mc) {
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
   
   private void removeConnections(PictogramElement pe) {
      removeConnections(pe, new DefaultRemoveFeature(getFeatureProvider()));
   }

   private void removeConnections(PictogramElement pe, DefaultRemoveFeature drf) {
      List<Connection> cons = Graphiti.getPeService().getOutgoingConnections((AnchorContainer) pe);
   
      for(Connection con : cons)
         drf.remove(new RemoveContext(con));
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
