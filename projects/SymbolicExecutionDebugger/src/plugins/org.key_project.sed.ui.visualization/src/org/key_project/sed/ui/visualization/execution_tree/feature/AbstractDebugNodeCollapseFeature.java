package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.debug.core.DebugException;
import org.eclipse.emf.common.util.EList;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.custom.AbstractCustomFeature;
import org.eclipse.graphiti.mm.pictograms.AnchorContainer;
import org.eclipse.graphiti.mm.pictograms.Connection;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.impl.AbstractSEDMethodCall;

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
      PictogramElement[] pes = context.getPictogramElements();
      
      if(pes != null && pes.length == 1)
      {
         Object bo = getBusinessObjectForPictogramElement(pes[0]);
         return canExecuteBusinessObject(bo);
      }
      
      return false;
   }
   
   /**
    * Checks if the give business object can be handled by this {@link ICustomFeature}.
    * @param businessObject The business object to check.
    * @return {@code true} can execute, {@code false} can not execute.
    */
   protected abstract boolean canExecuteBusinessObject(Object businessObject);
   
   /**
    * Executes the collapse feature. This function will recursivly iterate
    * over the childs and connections of the specific Element and hide them.
    */
   @Override
   public void execute(ICustomContext context) {
      PictogramElement[] pes = context.getPictogramElements();
      
      if(pes != null && pes.length == 1)
      {
         Object bo = getBusinessObjectForPictogramElement(pes[0]);
         
         if(bo instanceof AbstractSEDMethodCall)
         {
            AbstractSEDMethodCall node = (AbstractSEDMethodCall) bo;
            
            try {
               setMethodChildrenVisibility(node, node.isCollapsed());
               setConnectionVisibility((AnchorContainer) pes[0], node.isCollapsed());
               node.setIsCollapsed(!node.isCollapsed());
            }
            catch (DebugException e) {
               e.printStackTrace();
            }
         }
      }      
   }
   
   /**
    * This function hides or shows all children and connections of the given node, until
    * there are no more children or {@link ISEDMethodReturn} is reached.
    * @param node The current node
    * @param visible {@code true} shows the "methodbody" (expand), {@code false} hides the "methodbody" (collapse).
    * @throws DebugException
    */
   private void setMethodChildrenVisibility(ISEDDebugNode node, boolean visible) throws DebugException {
      ISEDDebugNode[] children = node.getChildren();
      
      if(children.length == 0)
         return;
      
      for(ISEDDebugNode child : children)
      {
         PictogramElement pe = getFeatureProvider().getPictogramElementForBusinessObject(child);

         if(!(child instanceof ISEDMethodReturn))
         {
            setMethodChildrenVisibility(child, visible);
            setConnectionVisibility((AnchorContainer) pe, visible);
         }

         pe.setVisible(visible);
      }
   }
   
   /**
    * This function hides or shows all outgoing connections of the given {@link AnchorContainer}
    * @param ac The {@link AnchorContainer} which provides the anchors of the connections
    * @param visible {@code true} shows the connections between the {@link AnchorContainer} and the childs,
    *                {@code false} hides the connections between the {@link AnchorContainer} and the childs
    */
   private void setConnectionVisibility(AnchorContainer ac, boolean visible) {
      EList<Connection> cons = ac.getAnchors().get(0).getOutgoingConnections();

      for(Connection con : cons)
         con.setVisible(visible);
   }
}
