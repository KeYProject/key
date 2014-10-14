package org.key_project.sed.ui.visualization.execution_tree.feature;

import java.awt.Color;
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
import org.eclipse.graphiti.mm.algorithms.styles.LineStyle;
import org.eclipse.graphiti.mm.pictograms.AnchorContainer;
import org.eclipse.graphiti.mm.pictograms.Connection;
import org.eclipse.graphiti.mm.pictograms.ConnectionDecorator;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.platform.IPlatformImageConstants;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.eclipse.graphiti.services.IPeCreateService;
import org.key_project.sed.core.model.ISEDBaseMethodReturn;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDLoopCondition;
import org.key_project.sed.core.model.ISEDLoopStatement;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.util.NodeUtil;
import org.key_project.sed.core.util.SEDLoopPreorderIterator;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeStyleUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.java.ArrayUtil;

public class LoopStatementCollapseFeature extends AbstractDebugNodeCollapseFeature {
   
   /**
    * The {@link SEDLoopPreorderIterator}
    */
   private SEDLoopPreorderIterator iter = null;
   
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

         UpdateContext uc = new UpdateContext(pes[0]);
         LoopStatementUpdateFeature uf = (LoopStatementUpdateFeature) getFeatureProvider().getUpdateFeature(uc);

         try
         {
            iter = new SEDLoopPreorderIterator(ls);
            
            if(!ls.isCollapsed()) {
               removeChildren(ls);
               removeConnections(pes[0]);
            }
            else {
               GraphicsAlgorithm ga = pes[0].getGraphicsAlgorithm();
               ga.setX(uf.METOFF);
               uf.update(uc);
            }

         }
         catch (DebugException e) {
            LogUtil.getLogger().logError(e);
         }
         
         ls.setCollapsed(!ls.isCollapsed());
      }
   }
   
   @Override
   protected void removeChildren(ISEDDebugNode node) throws DebugException {
      boolean firstNextIteration = false;
      DefaultRemoveFeature drf = new DefaultRemoveFeature(getFeatureProvider());
      PictogramElement lastIterNodePE = null;
      
      iter = new SEDLoopPreorderIterator((ISEDLoopStatement) node);
      while (iter.hasNext()) {
         ISEDDebugElement next = iter.next();
         
         if(next.equals(node)) {
            continue;
         }
         
         ISEDDebugNode nextNode = (ISEDDebugNode) next;

         if(iter.getIteration() != 2)
         {
            PictogramElement pe = getFeatureProvider().getPictogramElementForBusinessObject(nextNode);
            
            if(pe != null) {
               removeConnections(pe, drf);
               drf.remove(new RemoveContext(pe));
            }
         }
         
         if(iter.getIteration() == 3 && !firstNextIteration) {
            lastIterNodePE = getFeatureProvider().getPictogramElementForBusinessObject(NodeUtil.getParent(nextNode));
            
            if(lastIterNodePE != null) {
               removeConnections(lastIterNodePE, drf);
            }
            firstNextIteration = true;
         }
         
         if(!ArrayUtil.isEmpty(NodeUtil.getChildren(nextNode))) {
            if(NodeUtil.getChildren(nextNode)[0] == iter.getCurrentLoopLeaf() && lastIterNodePE != null) {
               createConnection((AnchorContainer) lastIterNodePE, (AnchorContainer) getFeatureProvider().getPictogramElementForBusinessObject(iter.getCurrentLoopLeaf()));
               lastIterNodePE = null;
               firstNextIteration = false;
            }
         }
      }
   }
   
   /*
    * TODO
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
      arrow.setLineStyle(LineStyle.DASH);
      arrow.setForeground(manageColor(255, 0, 0));

      Polyline polyline = gaService.createPolyline(connection);
      polyline.setStyle(ExecutionTreeStyleUtil.getStyleForParentConnection(getDiagram()));
      polyline.setLineStyle(LineStyle.DASH);
      polyline.setForeground(manageColor(255, 0, 0));
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
