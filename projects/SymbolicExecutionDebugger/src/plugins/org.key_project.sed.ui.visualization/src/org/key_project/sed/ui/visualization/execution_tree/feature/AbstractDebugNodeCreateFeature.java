package org.key_project.sed.ui.visualization.execution_tree.feature;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.ICreateFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.ICreateContext;
import org.eclipse.graphiti.features.impl.AbstractCreateFeature;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeFeatureProvider;
import org.key_project.sed.ui.visualization.execution_tree.service.SEDIndependenceSolver;
import org.key_project.sed.ui.visualization.execution_tree.wizard.CreateDebugNodeWizard;
import org.key_project.sed.ui.visualization.execution_tree.wizard.CreateDebugNodeWizard.CreateDebugNodeWizardResult;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * Provides a basic implementation of {@link ICreateFeature} for {@link ISEDDebugNode}s.
 * @author Martin Hentschel
 */
public abstract class AbstractDebugNodeCreateFeature extends AbstractCreateFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link ICreateFeature}.
    */
   public AbstractDebugNodeCreateFeature(IFeatureProvider fp, String name, String description) {
      super(fp, name, description);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canCreate(ICreateContext context) {
      return context.getTargetContainer() instanceof Diagram;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Object[] create(ICreateContext context) {
      try {
         // Ask user for initial values
         CreateDebugNodeWizardResult result = CreateDebugNodeWizard.openWizard(WorkbenchUtil.getActiveShell(), 
                                                                               getNodeType(),
                                                                               collectExistingNodes()); 
         if (result != null) {
            // Create new business object
            ISEDDebugNode newDebugNode = createNewDebugNode(result);

            // Do the add
            addGraphicalRepresentation(context, newDebugNode);

            // Return newly created business object(s)
            return new Object[] {newDebugNode};
         }
         else {
            return EMPTY;
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         return EMPTY;
      }
   }
   
   /**
    * Returns all existing {@link ISEDDebugNode}s in the {@link Diagram}.
    * @return All existing {@link ISEDDebugNode}s.
    */
   protected List<ISEDDebugNode> collectExistingNodes() {
      Assert.isTrue(getFeatureProvider() instanceof ExecutionTreeFeatureProvider);
      SEDIndependenceSolver solver = ((ExecutionTreeFeatureProvider)getFeatureProvider()).getSEDIndependenceSolver();
      Collection<Object> businessObjects = solver.getAllBusinessObjects();
      List<ISEDDebugNode> result = new LinkedList<ISEDDebugNode>();
      for (Object obj : businessObjects) {
         if (obj instanceof ISEDDebugNode) {
            result.add((ISEDDebugNode)obj);
         }
      }
      return result;
   }
   
   /**
    * Returns the name of the node type that is created via this {@link ICreateFeature}.
    * @return The node type name.
    */
   protected abstract String getNodeType();

   /**
    * Creates a new {@link ISEDDebugNode} to use as business object.
    * @param initialValues The initial values to use.
    * @return The created {@link ISEDDebugNode}.
    * @throws DebugException Occurred Exception.
    */
   protected abstract ISEDDebugNode createNewDebugNode(CreateDebugNodeWizardResult initialValues) throws DebugException;
}
