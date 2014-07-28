package org.key_project.sed.ui.visualization.execution_tree.feature;

import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.emf.common.util.EList;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.IUpdateFeature;
import org.eclipse.graphiti.features.context.ICustomContext;
import org.eclipse.graphiti.features.context.IRemoveContext;
import org.eclipse.graphiti.features.context.IUpdateContext;
import org.eclipse.graphiti.features.context.impl.AddContext;
import org.eclipse.graphiti.features.context.impl.AreaContext;
import org.eclipse.graphiti.features.context.impl.RemoveContext;
import org.eclipse.graphiti.features.context.impl.UpdateContext;
import org.eclipse.graphiti.features.custom.AbstractCustomFeature;
import org.eclipse.graphiti.features.impl.DefaultRemoveFeature;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.algorithms.Polyline;
import org.eclipse.graphiti.mm.algorithms.Rectangle;
import org.eclipse.graphiti.mm.pictograms.Anchor;
import org.eclipse.graphiti.mm.pictograms.AnchorContainer;
import org.eclipse.graphiti.mm.pictograms.ChopboxAnchor;
import org.eclipse.graphiti.mm.pictograms.Connection;
import org.eclipse.graphiti.mm.pictograms.ConnectionDecorator;
import org.eclipse.graphiti.mm.pictograms.ContainerShape;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.mm.pictograms.Shape;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.eclipse.graphiti.services.IPeCreateService;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.impl.AbstractSEDBranchStatement;
import org.key_project.sed.core.model.impl.AbstractSEDMethodCall;
import org.key_project.sed.core.model.memory.SEDMemoryBranchStatement;
import org.key_project.sed.core.model.memory.SEDMemoryMethodCall;
import org.key_project.sed.core.model.memory.SEDMemoryMethodReturn;
import org.key_project.sed.core.model.memory.SEDMemoryStatement;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeStyleUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;

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
   
//   /**
//    * Executes the collapse feature. This function will recursivly iterate
//    * over the childs and connections of the specific Element and hide them.
//    */
//   @Override
//   public void execute(ICustomContext context) {
//      PictogramElement[] pes = context.getPictogramElements();
//      
//      if(pes != null && pes.length == 1)
//      {
//         Object bo = getBusinessObjectForPictogramElement(pes[0]);
//         
//         if(bo instanceof AbstractSEDMethodCall)
//         {
//            System.out.println(bo.getClass());
//            AbstractSEDMethodCall node = (AbstractSEDMethodCall) bo;
//
//            PictogramElement pe = getFeatureProvider().getPictogramElementForBusinessObject(bo);
//            ContainerShape parentContainer = (ContainerShape) pe;
//            Rectangle rect = (Rectangle) parentContainer.getChildren().get(0).getGraphicsAlgorithm();
//
//            boolean isCollapsed = Boolean.parseBoolean(Graphiti.getPeService().getPropertyValue(pe, "collapsed"));
////            System.out.println("isCol: " + Boolean.parseBoolean(Graphiti.getPeService().getPropertyValue(pe, "collapsed")));
//            GraphicsAlgorithm ga = pes[0].getGraphicsAlgorithm();
//            int OFFSET = getDiagram().getGridUnit() * 2;
//            int height = 3 * ga.getHeight() + 2 * OFFSET;
//            
//            try {
//               if(!isCollapsed)
//               {
//                  Set<ISEDDebugNode> closures = removeChildren(node, node.getId(), new LinkedHashSet<ISEDDebugNode>());
//                  removeConnections(pes[0]);
////                  
////                  DefaultRemoveFeature drf = new DefaultRemoveFeature(getFeatureProvider());
////                  drf.remove(new RemoveContext(pes[0]));
//
//                  int methodHeight = Integer.parseInt(Graphiti.getPeService().getPropertyValue(pe, "height"));
//                  int diff = methodHeight - height;
////                  System.out.println("MH: " + methodHeight + ", H: " + height + ", Diff: " + diff);
//
//                  if(methodHeight > height){
//                     parentContainer.getGraphicsAlgorithm().setHeight(height);
//                     rect.setHeight(height - ga.getHeight());
//                     
//                     SEDMemoryStatement mc = new SEDMemoryStatement(node.getDebugTarget(), null, node.getThread());
//                     mc.setName(node.getName());
//                     AreaContext areaContext = new AreaContext();
//                     areaContext.setX(pes[0].getGraphicsAlgorithm().getX());
//                     areaContext.setY(pes[0].getGraphicsAlgorithm().getY());
//                     
//                     AddContext addContext = new AddContext(areaContext, mc);
//                     addContext.setTargetContainer(getDiagram());
//                     // Execute add feature manually because getFeatureProvider().addIfPossible(addContext) changes the selection
//                     IAddFeature feature = getFeatureProvider().getAddFeature(addContext);
//                     if (feature != null && feature.canExecute(addContext)) {
//                        feature.execute(addContext);
//                     }
//                     PictogramElement mcPE = getFeatureProvider().getPictogramElementForBusinessObject(mc);
////                     isInMethod = Boolean.parseBoolean(Graphiti.getPeService().getPropertyValue(pe, "isInMethod"));
//
////                     Graphiti.getPeService().setPropertyValue(mcPE, "isInMethod", "true");
//                     mcPE.setVisible(false);
//
//                     int offset = 0;
//                     int x = 0;
//                     LinkedList<ISEDDebugNode> toUpdate = new LinkedList<ISEDDebugNode>();
//                     for(ISEDDebugNode closure : closures) {
//
//                        SEDMemoryBranchStatement bs = new SEDMemoryBranchStatement(node.getDebugTarget(), mc, node.getThread());
//                        bs.setName(closure.getPathCondition());
////                        bs.setName("EIN_WIRKLICH_SUPER_DUPER_MEGA_BOMBASTISCHER_SAU_LANGER_NAME");
//                        mc.addChild(bs);
////                      AreaContext areaContext = new AreaContext();
////                      areaContext.setX(x);
////                      areaContext.setY(parentContainer.getGraphicsAlgorithm().getY() + ga.getHeight() + OFFSET);
////                      
////                      AddContext addContext = new AddContext(areaContext, bs);
////                      addContext.setTargetContainer(getDiagram());
////                      // Execute add feature manually because getFeatureProvider().addIfPossible(addContext) changes the selection
////                      IAddFeature feature = getFeatureProvider().getAddFeature(addContext);
////                      if (feature != null && feature.canExecute(addContext)) {
////                         feature.execute(addContext);
////                      }
//                        
//                        SEDMemoryMethodReturn mr = new SEDMemoryMethodReturn(closure.getDebugTarget(), bs, closure.getThread());
//                        mr.setName(closure.getName());
//                        bs.addChild(mr);
////                        toUpdate.add(bs);
////                        
////                        AreaContext areaContext = new AreaContext();
////                        areaContext.setX(x);
////                        areaContext.setY(parentContainer.getGraphicsAlgorithm().getY() + 2 * (ga.getHeight() + OFFSET));
////                        
////                        AddContext addContext = new AddContext(areaContext, mr);
////                        addContext.setTargetContainer(getDiagram());
////                        // Execute add feature manually because getFeatureProvider().addIfPossible(addContext) changes the selection
////                        IAddFeature feature = getFeatureProvider().getAddFeature(addContext);
////                        if (feature != null && feature.canExecute(addContext)) {
////                           feature.execute(addContext);
////                        }
////                        
////                        
////                        
////                        
////                        
////                        PictogramElement closurePE = getFeatureProvider().getPictogramElementForBusinessObject(closure);
////                        GraphicsAlgorithm closureGA = closurePE.getGraphicsAlgorithm();
////                        closureGA.setY(closureGA.getY() - diff);
////                        
////                        
////                        areaContext = new AreaContext();
////                        areaContext.setX(closureGA.getX());
////                        areaContext.setY(parentContainer.getGraphicsAlgorithm().getY() + ga.getHeight() + OFFSET);
////                        
////                        AddContext addContext = new AddContext(areaContext, bs);
////                        addContext.setTargetContainer(getDiagram());
////                        // Execute add feature manually because getFeatureProvider().addIfPossible(addContext) changes the selection
////                        IAddFeature feature = getFeatureProvider().getAddFeature(addContext);
////                        if (feature != null && feature.canExecute(addContext)) {
////                           feature.execute(addContext);
////                        }
//
////                        System.out.println(Arrays.toString(node.getChildren()));
////                        System.out.println("Clo: " + closure + ", PE: " + closurePE);
////                        
////                        PictogramElement branchPE = getFeatureProvider().getPictogramElementForBusinessObject(bs);
////                        GraphicsAlgorithm branchGA = branchPE.getGraphicsAlgorithm();
////                        
////                        int centerX = closureGA.getX() + closureGA.getWidth() / 2 - branchPE.getGraphicsAlgorithm().getWidth() / 2;
////                        
////                        if(branchGA.getWidth() > closureGA.getWidth()) {
////                           offset += closureGA.getX() - centerX;
////                        }
////                        
////                        branchGA.setX(centerX + offset);
//                        
//                        
//                        
////                        branchPE.getGraphicsAlgorithm().setX(closureGA.getX() + closureGA.getWidth() / 2 - branchPE.getGraphicsAlgorithm().getWidth() / 2);
//
////                        createConnection((AnchorContainer) branchPE, (AnchorContainer) closurePE);
//                     }
//                     
////                     UpdateContext uc = new UpdateContext(getFeatureProvider().getPictogramElementForBusinessObject(toUpdate.getFirst()));
//                     UpdateContext uc = new UpdateContext(getFeatureProvider().getPictogramElementForBusinessObject(mc));
//                     AbstractDebugNodeUpdateFeature feature1 = (AbstractDebugNodeUpdateFeature) getFeatureProvider().getUpdateFeature(uc);
//                     feature1.update(uc);
//                     
//                     ga.setX(mcPE.getGraphicsAlgorithm().getX());
//                     
//                     uc = new UpdateContext(pes[0]);
//                     feature1 = (AbstractDebugNodeUpdateFeature) getFeatureProvider().getUpdateFeature(uc);
//                     
//                     IProgressMonitor monitor = GraphitiUtil.getProgressMonitor(context);
//                     feature1.updateParents(pes[0], OFFSET, new SubProgressMonitor(monitor, 1));
////                     Set<ISEDDebugNode> leafs = feature1.updateChildrenLeftAligned(node, new SubProgressMonitor(monitor, 1), getDiagram().getGridUnit() * 2, 0);
//                     monitor.worked(1);
////                     leafs.addAll(closures);
////                     System.out.println(closures);
////                     feature1.centerChildren(leafs, new SubProgressMonitor(monitor, 1));
////                     monitor.worked(1);
//                     monitor.done();
//
//                     Graphiti.getPeService().setPropertyValue(pe, "height", Integer.toString(height));
//                  }
//               }
//               else {
//                  DefaultRemoveFeature drf = new DefaultRemoveFeature(getFeatureProvider());
//                  List<Connection> cons = Graphiti.getPeService().getOutgoingConnections((AnchorContainer) pes[0]);
//                  
//                  for(Connection con : cons) {
//                     PictogramElement branchPE = con.getEnd().getParent();
//                     if(branchPE != null) {
//                        removeConnections(branchPE, drf);
//                        drf.remove(new RemoveContext(branchPE));
//                     }
//                  }
//                  
//                  removeConnections(pes[0]);
//
//                  Set<ISEDDebugNode> closures = removeChildren(node, node.getId(), new LinkedHashSet<ISEDDebugNode>());
////                  Set<Shape> closures = new LinkedHashSet<Shape>();
////                  for(int i = 2; i < parentContainer.getChildren().size(); i++) {
////                     closures.add(parentContainer.getChildren().get(i));
////                  }
//
//                  UpdateContext uc = new UpdateContext(pes[0]);
//                  AbstractDebugNodeUpdateFeature feature = (AbstractDebugNodeUpdateFeature) getFeatureProvider().getUpdateFeature(uc);
//                  IProgressMonitor monitor = GraphitiUtil.getProgressMonitor(context);
//                  Set<ISEDDebugNode> leafs = feature.updateChildrenLeftAligned(node, new SubProgressMonitor(monitor, 1), getDiagram().getGridUnit() * 2, 0);
//                  monitor.worked(1);
//                  leafs.addAll(closures);
////                  System.out.println(closures);
//                  feature.centerChildren(leafs, new SubProgressMonitor(monitor, 1));
//                  monitor.worked(1);
//                  monitor.done();
//                  
//                  GraphicsAlgorithm pga = parentContainer.getGraphicsAlgorithm();
//                  pga.setHeight(pga.getHeight() + ga.getHeight() + 2 * getDiagram().getGridUnit());
//                  rect.setHeight(pga.getHeight() - ga.getHeight());
//                  
//                  for(ISEDDebugNode closure : closures) {
//                     PictogramElement closurePE = getFeatureProvider().getPictogramElementForBusinessObject(closure);
//                     closurePE.getGraphicsAlgorithm().setY(rect.getHeight());
//                     createConnection((AnchorContainer) getFeatureProvider().getPictogramElementForBusinessObject(closure.getParent()), (AnchorContainer) closurePE);
//                  }
//
//                  Graphiti.getPeService().setPropertyValue(pe, "height", Integer.toString(pga.getHeight()));
//               }
//               
//               Graphiti.getPeService().setPropertyValue(pe, "collapsed", String.valueOf(!isCollapsed));
//            }
//            catch (DebugException e) {
//               e.printStackTrace();
//            }
//         }
//      }      
//   }
//   
//   private void createConnection(AnchorContainer startAC, AnchorContainer endAC) {
//      IPeCreateService peCreateService = Graphiti.getPeCreateService();
//      IGaService gaService = Graphiti.getGaService();
//
//      Connection connection = peCreateService.createFreeFormConnection(getDiagram());
//      connection.setStart(startAC.getAnchors().get(0));
//      connection.setEnd(endAC.getAnchors().get(0));
//      
//      ConnectionDecorator cd = peCreateService.createConnectionDecorator(connection, false, 1.0, true);
//      Polyline arrow = gaService.createPolyline(cd, new int[] {-10, 5, 0, 0, -10, -5});
//      arrow.setStyle(ExecutionTreeStyleUtil.getStyleForParentConnection(getDiagram()));
//
//      Polyline polyline = gaService.createPolyline(connection);
//      polyline.setStyle(ExecutionTreeStyleUtil.getStyleForParentConnection(getDiagram()));
//   }
//   
//   /**
//    * This function removes all children and connections of the given node, until
//    * there are no more children or {@link ISEDMethodReturn} is reached and returns
//    * all found MethodReturns.
//    * @param ISEDDebugNode node The current node
//    * @return Set<ISEDDebugNode> methodCloses Contains all MethodReturns
//    * @throws DebugException
//    */
//   private Set<ISEDDebugNode> removeChildren(ISEDDebugNode node, String methodID, Set<ISEDDebugNode> methodCloses) throws DebugException {
//      ISEDDebugNode[] children = node.getChildren();
//      
//      if(children.length == 0)
//         return methodCloses;
//      
//      DefaultRemoveFeature drf = new DefaultRemoveFeature(getFeatureProvider());
//      
//      for(ISEDDebugNode child : children)
//      {
//         PictogramElement pe = getFeatureProvider().getPictogramElementForBusinessObject(child);
//         String mID = Graphiti.getPeService().getPropertyValue(pe, "methodID");
//         
//         if(child instanceof ISEDMethodReturn && mID.equals(methodID))
//         {
//            methodCloses.add(child);
//            removeConnections(pe, drf);
//            drf.remove(new RemoveContext(pe));
//            continue;
//         }
//         
//         methodCloses.addAll(removeChildren(child, methodID, methodCloses));
//         
//         if(pe != null) {
//            removeConnections(pe, drf);
//            drf.remove(new RemoveContext(pe));
//         }
//      }
//      
//      return methodCloses;
//   }
//   
//   private void removeConnections(PictogramElement pe) {
//      removeConnections(pe, new DefaultRemoveFeature(getFeatureProvider()));
//   }
//   
//   private void removeConnections(PictogramElement pe, DefaultRemoveFeature drf) {
//      List<Connection> cons = Graphiti.getPeService().getOutgoingConnections((AnchorContainer) pe);
//      
//      for(Connection con : cons)
//         drf.remove(new RemoveContext(con));
//   }
}
