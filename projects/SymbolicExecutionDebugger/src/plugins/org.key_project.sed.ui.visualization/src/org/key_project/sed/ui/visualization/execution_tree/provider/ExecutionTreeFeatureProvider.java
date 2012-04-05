package org.key_project.sed.ui.visualization.execution_tree.provider;

import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.ICreateFeature;
import org.eclipse.graphiti.features.IDeleteFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.ILayoutFeature;
import org.eclipse.graphiti.features.IRemoveFeature;
import org.eclipse.graphiti.features.context.IAddContext;
import org.eclipse.graphiti.features.context.IDeleteContext;
import org.eclipse.graphiti.features.context.ILayoutContext;
import org.eclipse.graphiti.features.context.IRemoveContext;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.ui.features.DefaultFeatureProvider;
import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDBranchNode;
import org.key_project.sed.core.model.ISEDExceptionalTermination;
import org.key_project.sed.core.model.ISEDLoopCondition;
import org.key_project.sed.core.model.ISEDLoopNode;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.ui.visualization.execution_tree.feature.BranchConditionAddFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.BranchConditionCreateFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.BranchConditionLayoutFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.BranchNodeAddFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.BranchNodeCreateFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.BranchNodeLayoutFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.ExceptionalTerminationAddFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.ExceptionalTerminationCreateFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.ExceptionalTerminationLayoutFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.LoopConditionAddFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.LoopConditionCreateFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.LoopConditionLayoutFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.LoopNodeAddFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.LoopNodeCreateFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.LoopNodeLayoutFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.MethodCallAddFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.MethodCallCreateFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.MethodCallLayoutFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.MethodReturnAddFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.MethodReturnCreateFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.MethodReturnLayoutFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.ExecutionTreeDeleteFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.ExecutionTreeRemoveFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.StatementAddFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.StatementCreateFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.StatementLayoutFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.TerminationAddFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.TerminationCreateFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.TerminationLayoutFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.ThreadAddFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.ThreadCreateFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.ThreadLayoutFeature;
import org.key_project.sed.ui.visualization.execution_tree.service.SEDIndependenceSolver;

/**
 * {@link IFeatureProvider} specific implementation for execution tree diagrams.
 * @author Martin Hentschel
 */
public class ExecutionTreeFeatureProvider extends DefaultFeatureProvider {
   /**
    * Constructor.
    * @param dtp The diagram type provider for that this {@link IFeatureProvider} is used.
    */
   public ExecutionTreeFeatureProvider(IDiagramTypeProvider dtp) {
      super(dtp);
      setIndependenceSolver(new SEDIndependenceSolver());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ICreateFeature[] getCreateFeatures() {
      return new ICreateFeature[] {new BranchConditionCreateFeature(this),
                                   new BranchNodeCreateFeature(this),
                                   new ExceptionalTerminationCreateFeature(this),
                                   new LoopConditionCreateFeature(this),
                                   new LoopNodeCreateFeature(this),
                                   new MethodCallCreateFeature(this),
                                   new MethodReturnCreateFeature(this),
                                   new StatementCreateFeature(this),
                                   new TerminationCreateFeature(this),
                                   new ThreadCreateFeature(this)};
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IAddFeature getAddFeature(IAddContext context) {
      if (context.getNewObject() instanceof ISEDBranchCondition) {
          return new BranchConditionAddFeature(this);
      }
      else if (context.getNewObject() instanceof ISEDBranchNode) {
         return new BranchNodeAddFeature(this);
      }
      else if (context.getNewObject() instanceof ISEDExceptionalTermination) {
         return new ExceptionalTerminationAddFeature(this);
      }
      else if (context.getNewObject() instanceof ISEDLoopCondition) {
         return new LoopConditionAddFeature(this);
      }
      else if (context.getNewObject() instanceof ISEDLoopNode) {
         return new LoopNodeAddFeature(this);
      }
      else if (context.getNewObject() instanceof ISEDMethodCall) {
         return new MethodCallAddFeature(this);
      }
      else if (context.getNewObject() instanceof ISEDMethodReturn) {
         return new MethodReturnAddFeature(this);
      }
      else if (context.getNewObject() instanceof ISEDStatement) {
         return new StatementAddFeature(this);
      }
      else if (context.getNewObject() instanceof ISEDTermination) {
         return new TerminationAddFeature(this);
      }
      else if (context.getNewObject() instanceof ISEDThread) {
         return new ThreadAddFeature(this);
      }
      else {
         return super.getAddFeature(context);
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public ILayoutFeature getLayoutFeature(ILayoutContext context) {
      PictogramElement pictogramElement = context.getPictogramElement();
      Object bo = getBusinessObjectForPictogramElement(pictogramElement);
      if (bo instanceof ISEDBranchCondition) {
          return new BranchConditionLayoutFeature(this);
      }
      else if (bo instanceof ISEDBranchNode) {
         return new BranchNodeLayoutFeature(this);
      }
      else if (bo instanceof ISEDExceptionalTermination) {
         return new ExceptionalTerminationLayoutFeature(this);
      }
      else if (bo instanceof ISEDLoopCondition) {
         return new LoopConditionLayoutFeature(this);
      }
      else if (bo instanceof ISEDLoopNode) {
         return new LoopNodeLayoutFeature(this);
      }
      else if (bo instanceof ISEDMethodCall) {
         return new MethodCallLayoutFeature(this);
      }
      else if (bo instanceof ISEDMethodReturn) {
         return new MethodReturnLayoutFeature(this);
      }
      else if (bo instanceof ISEDStatement) {
         return new StatementLayoutFeature(this);
      }
      else if (bo instanceof ISEDTermination) {
         return new TerminationLayoutFeature(this);
      }
      else if (bo instanceof ISEDThread) {
         return new ThreadLayoutFeature(this);
      }
      else {
         return super.getLayoutFeature(context);
      }
   }
   
   @Override
   public IDeleteFeature getDeleteFeature(IDeleteContext context) {
      return new ExecutionTreeDeleteFeature(this);
   }

   @Override
   public IRemoveFeature getRemoveFeature(IRemoveContext context) {
      return new ExecutionTreeRemoveFeature(this);
   }
   
   /**
    * Returns the used {@link SEDIndependenceSolver}.
    * @return The used {@link SEDIndependenceSolver}.
    */
   public SEDIndependenceSolver getSEDIndependenceSolver() {
      return (SEDIndependenceSolver)getIndependenceSolver();
   }
}