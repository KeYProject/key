package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.ICreateFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.core.model.memory.SEDMemoryTermination;
import org.key_project.sed.ui.visualization.execution_tree.provider.IExecutionTreeImageConstants;
import org.key_project.sed.ui.visualization.execution_tree.wizard.CreateDebugNodeWizard.CreateDebugNodeWizardResult;

/**
 * Implementation of {@link ICreateFeature} for {@link ISEDTermination}s.
 * @author Martin Hentschel
 */
public class TerminationCreateFeature extends AbstractDebugNodeCreateFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public TerminationCreateFeature(IFeatureProvider fp) {
       super(fp, "Termination", "Create a new Termination");
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getCreateImageId() {
      return IExecutionTreeImageConstants.IMG_TERMINATION;
   }
   
   /**
    * {@inheritDoc}
    */   
   @Override
   public String getNodeType() {
      return "Termination";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ISEDDebugNode createNewDebugNode(CreateDebugNodeWizardResult initialValues) throws DebugException {
      ISEDDebugNode parent = initialValues.getParent();
      Assert.isNotNull(parent);
      SEDMemoryTermination result = new SEDMemoryTermination(parent.getDebugTarget(), parent, parent.getThread());
      result.setName(initialValues.getName());
      return result;
   }
}