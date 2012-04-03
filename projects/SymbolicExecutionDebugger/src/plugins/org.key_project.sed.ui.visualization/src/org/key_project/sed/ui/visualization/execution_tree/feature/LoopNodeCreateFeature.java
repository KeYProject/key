package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.ICreateFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDLoopNode;
import org.key_project.sed.core.model.memory.SEDMemoryLoopNode;
import org.key_project.sed.ui.visualization.execution_tree.provider.IExecutionTreeImageConstants;
import org.key_project.sed.ui.visualization.execution_tree.wizard.CreateDebugNodeWizard.CreateDebugNodeWizardResult;

/**
 * Implementation of {@link ICreateFeature} for {@link ISEDLoopNode}s.
 * @author Martin Hentschel
 */
public class LoopNodeCreateFeature extends AbstractDebugNodeCreateFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public LoopNodeCreateFeature(IFeatureProvider fp) {
       super(fp, "Loop Node", "Create a new Loop Node");
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getCreateImageId() {
      return IExecutionTreeImageConstants.IMG_LOOP_NODE;
   }
   
   /**
    * {@inheritDoc}
    */   
   @Override
   public String getNodeType() {
      return "Loop Node";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ISEDDebugNode createNewDebugNode(CreateDebugNodeWizardResult initialValues) throws DebugException {
      ISEDDebugNode parent = initialValues.getParent();
      Assert.isNotNull(parent);
      SEDMemoryLoopNode result = new SEDMemoryLoopNode(parent.getDebugTarget(), parent, parent.getThread());
      result.setName(initialValues.getName());
      return result;
   }

}