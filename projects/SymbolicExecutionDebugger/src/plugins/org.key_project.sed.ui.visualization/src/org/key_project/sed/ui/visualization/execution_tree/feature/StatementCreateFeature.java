package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.ICreateFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.memory.ISEDMemoryDebugNode;
import org.key_project.sed.core.model.memory.SEDMemoryStatement;
import org.key_project.sed.ui.visualization.execution_tree.provider.IExecutionTreeImageConstants;
import org.key_project.sed.ui.visualization.execution_tree.wizard.CreateDebugNodeWizard.CreateDebugNodeWizardResult;
import org.key_project.sed.ui.visualization.util.LogUtil;

/**
 * Implementation of {@link ICreateFeature} for {@link ISEDStatement}s.
 * @author Martin Hentschel
 */
public class StatementCreateFeature extends AbstractDebugNodeCreateFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public StatementCreateFeature(IFeatureProvider fp) {
       super(fp, "Statement", "Create a new Statement");
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getCreateImageId() {
      return IExecutionTreeImageConstants.IMG_STATEMENT;
   }
   
   /**
    * {@inheritDoc}
    */   
   @Override
   public String getNodeType() {
      return "Statement";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ISEDDebugNode createNewDebugNode(CreateDebugNodeWizardResult initialValues) throws DebugException {
      ISEDDebugNode parent = initialValues.getParent();
      Assert.isNotNull(parent);
      SEDMemoryStatement result = new SEDMemoryStatement(parent.getDebugTarget(), parent, parent.getThread());
      result.setName(initialValues.getName());
      if (!(parent instanceof ISEDMemoryDebugNode)) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus("Unsupported parent \"" + parent + "\"."));
      }
      ((ISEDMemoryDebugNode)parent).addChild(result);
      return result;
   }
}