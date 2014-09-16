package org.key_project.sed.ui.visualization.execution_tree.feature;

import java.util.List;

import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.impl.RemoveContext;
import org.eclipse.graphiti.features.custom.AbstractCustomFeature;
import org.eclipse.graphiti.features.impl.DefaultRemoveFeature;
import org.eclipse.graphiti.mm.algorithms.Polyline;
import org.eclipse.graphiti.mm.pictograms.AnchorContainer;
import org.eclipse.graphiti.mm.pictograms.Connection;
import org.eclipse.graphiti.mm.pictograms.ConnectionDecorator;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.eclipse.graphiti.services.IPeCreateService;
import org.key_project.sed.core.model.ISEDBaseMethodReturn;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.util.ISEDIterator;
import org.key_project.sed.core.util.SEDMethodPreorderIterator;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeStyleUtil;
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
    * TODO
    * This function removes all children and connections of the given node, until
    * there are no more children or either {@link ISEDMethodReturn} is reached for
    * {@link ISEDMethodCall} or the last {@link ISEDLoopCondition} for
    * {@link ISEDLoopStatement}.
    * @param ISEDDebugNode node The current node
    * @throws DebugException
    */
   protected abstract void removeChildren(ISEDDebugNode node) throws DebugException;
   
   /*
    * TODO
    */
   protected void removeConnections(PictogramElement pe) {
      removeConnections(pe, new DefaultRemoveFeature(getFeatureProvider()));
   }

   /*
    * TODO
    */
   protected void removeConnections(PictogramElement pe, DefaultRemoveFeature drf) {
      List<Connection> cons = Graphiti.getPeService().getOutgoingConnections((AnchorContainer) pe);
   
      for(Connection con : cons)
         drf.remove(new RemoveContext(con));
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

      Polyline polyline = gaService.createPolyline(connection);
      polyline.setStyle(ExecutionTreeStyleUtil.getStyleForParentConnection(getDiagram()));
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
}
