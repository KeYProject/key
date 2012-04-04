package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.ICreateFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.memory.ISEDMemoryDebugNode;
import org.key_project.sed.core.model.memory.SEDMemoryMethodReturn;
import org.key_project.sed.ui.visualization.execution_tree.provider.IExecutionTreeImageConstants;
import org.key_project.sed.ui.visualization.execution_tree.wizard.CreateDebugNodeWizard.CreateDebugNodeWizardResult;
import org.key_project.sed.ui.visualization.util.LogUtil;

/**
 * Implementation of {@link ICreateFeature} for {@link ISEDMethodReturn}s.
 * @author Martin Hentschel
 */
public class MethodReturnCreateFeature extends AbstractDebugNodeCreateFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public MethodReturnCreateFeature(IFeatureProvider fp) {
       super(fp, "Method Return", "Create a new Method Return");
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getCreateImageId() {
      return IExecutionTreeImageConstants.IMG_METHOD_RETURN;
   }
   
   /**
    * {@inheritDoc}
    */   
   @Override
   public String getNodeType() {
      return "Method Return";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ISEDDebugNode createNewDebugNode(CreateDebugNodeWizardResult initialValues) throws DebugException {
      ISEDDebugNode parent = initialValues.getParent();
      Assert.isNotNull(parent);
      SEDMemoryMethodReturn result = new SEDMemoryMethodReturn(parent.getDebugTarget(), parent, parent.getThread());
      result.setName(initialValues.getName());
      if (!(parent instanceof ISEDMemoryDebugNode)) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus("Unsupported parent \"" + parent + "\"."));
      }
      ((ISEDMemoryDebugNode)parent).addChild(result);      
      return result;
   }
}