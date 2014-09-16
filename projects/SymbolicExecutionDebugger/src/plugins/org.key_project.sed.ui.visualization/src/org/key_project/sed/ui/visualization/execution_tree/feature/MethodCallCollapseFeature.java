package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.impl.RemoveContext;
import org.eclipse.graphiti.features.context.impl.UpdateContext;
import org.eclipse.graphiti.features.impl.DefaultRemoveFeature;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.platform.IPlatformImageConstants;
import org.eclipse.graphiti.util.ColorConstant;
import org.key_project.sed.core.model.ISEDBaseMethodReturn;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.util.ISEDIterator;
import org.key_project.sed.core.util.SEDMethodPreorderIterator;
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
         ISEDMethodCall mc = (ISEDMethodCall) getBusinessObjectForPictogramElement(pes[0]);
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

               uf.updateCollapse(mc, monitor);
            }
            else {
               color = new ColorConstant(102, 80, 180);
               uf.updateExpand(mc, monitor);
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
