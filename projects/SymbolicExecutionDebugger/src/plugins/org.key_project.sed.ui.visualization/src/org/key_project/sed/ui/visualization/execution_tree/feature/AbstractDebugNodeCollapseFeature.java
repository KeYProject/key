package org.key_project.sed.ui.visualization.execution_tree.feature;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.custom.AbstractCustomFeature;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.algorithms.Rectangle;
import org.eclipse.graphiti.mm.pictograms.AnchorContainer;
import org.eclipse.graphiti.mm.pictograms.Connection;
import org.eclipse.graphiti.mm.pictograms.ContainerShape;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.services.Graphiti;
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
            
            ContainerShape parentContainer = (ContainerShape) pes[0].eContainer();
            ContainerShape methodContainer = (ContainerShape) parentContainer.getChildren().get(0);
            Rectangle rect = (Rectangle) methodContainer.getGraphicsAlgorithm();
            
            PictogramElement pe = (PictogramElement) pes[0].eContainer();
//            boolean isCollapsed = Boolean.parseBoolean(Graphiti.getPeService().getPropertyValue(pes[0], "collapsed"));
            boolean isCollapsed = Boolean.parseBoolean(Graphiti.getPeService().getPropertyValue(pe, "collapsed"));
            try {
               Set<ISEDDebugNode> closures = setMethodChildrenVisibility(node, isCollapsed, new LinkedHashSet<ISEDDebugNode>());
               setConnectionVisibility((AnchorContainer) pe, isCollapsed);
               Graphiti.getPeService().setPropertyValue(pe, "collapsed", String.valueOf(!isCollapsed));
               
               GraphicsAlgorithm ga = pes[0].getGraphicsAlgorithm();
               int methodHeight = Integer.parseInt(Graphiti.getPeService().getPropertyValue(pe, "height"));
               int height = 2 * (ga.getHeight() + getDiagram().getGridUnit());
               int diff = methodHeight - height;
               
               if(!isCollapsed)
               {
                  if(methodHeight > height){
                     parentContainer.getGraphicsAlgorithm().setHeight(height);
                     rect.setHeight(height - ga.getHeight());
                     
                     for(ISEDDebugNode child : closures) {
                        System.out.println(child);
                        PictogramElement pic = getFeatureProvider().getPictogramElementForBusinessObject(child);
                        pic.getGraphicsAlgorithm().setY(pic.getGraphicsAlgorithm().getY() - diff);
                     }
                  }
               }
               else
               {
                  parentContainer.getGraphicsAlgorithm().setHeight(methodHeight);
                  rect.setHeight(methodHeight - ga.getHeight());
                  
                  for(ISEDDebugNode child : closures) {
                     System.out.println(child);
                     PictogramElement pic = getFeatureProvider().getPictogramElementForBusinessObject(child);
                     pic.getGraphicsAlgorithm().setY(pic.getGraphicsAlgorithm().getY() + diff);
                  }
               }
               

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
   private Set<ISEDDebugNode> setMethodChildrenVisibility(ISEDDebugNode node, boolean visible, Set<ISEDDebugNode> methodCloses) throws DebugException {
      ISEDDebugNode[] children = node.getChildren();
      
      if(children.length == 0)
         return methodCloses;
      
      for(ISEDDebugNode child : children)
      {
         if(child instanceof ISEDMethodReturn)
         {
            methodCloses.add(child);
            continue;
         }
         
         PictogramElement pe = getFeatureProvider().getPictogramElementForBusinessObject(child);

         methodCloses.addAll(setMethodChildrenVisibility(child, visible, methodCloses));
         setConnectionVisibility((AnchorContainer) pe, visible);

         pe.setVisible(visible);
      }
      System.out.println("hallo");
      for(ISEDDebugNode child : methodCloses) {
         System.out.println(child);
      }
      
      return methodCloses;
   }
   
   /**
    * This function hides or shows all outgoing connections of the given {@link AnchorContainer}
    * @param ac The {@link AnchorContainer} which provides the anchors of the connections
    * @param visible {@code true} shows the connections between the {@link AnchorContainer} and the childs,
    *                {@code false} hides the connections between the {@link AnchorContainer} and the childs
    */
   private void setConnectionVisibility(AnchorContainer ac, boolean visible) {
      List<Connection> cons = Graphiti.getPeService().getOutgoingConnections(ac);//ac.getAnchors().get(0).getOutgoingConnections();

      for(Connection con : cons)
         con.setVisible(visible);
   }
}
