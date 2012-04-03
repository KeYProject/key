package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.ICreateFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDLoopCondition;
import org.key_project.sed.core.model.memory.SEDMemoryLoopCondition;
import org.key_project.sed.ui.visualization.execution_tree.provider.IExecutionTreeImageConstants;
import org.key_project.sed.ui.visualization.execution_tree.wizard.CreateDebugNodeWizard.CreateDebugNodeWizardResult;

/**
 * Implementation of {@link ICreateFeature} for {@link ISEDLoopCondition}s.
 * @author Martin Hentschel
 */
public class LoopConditionCreateFeature extends AbstractDebugNodeCreateFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public LoopConditionCreateFeature(IFeatureProvider fp) {
       super(fp, "Loop Condition", "Create a new Loop Condition");
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getCreateImageId() {
      return IExecutionTreeImageConstants.IMG_LOOP_CONDITION;
   }
   
   /**
    * {@inheritDoc}
    */   
   @Override
   public String getNodeType() {
      return "Loop Condition";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ISEDDebugNode createNewDebugNode(CreateDebugNodeWizardResult initialValues) throws DebugException {
      ISEDDebugNode parent = initialValues.getParent();
      Assert.isNotNull(parent);
      SEDMemoryLoopCondition result = new SEDMemoryLoopCondition(parent.getDebugTarget(), parent, parent.getThread());
      result.setName(initialValues.getName());
      return result;
   }

}