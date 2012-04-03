package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.ICreateFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDExceptionalTermination;
import org.key_project.sed.core.model.memory.SEDMemoryExceptionalTermination;
import org.key_project.sed.ui.visualization.execution_tree.provider.IExecutionTreeImageConstants;
import org.key_project.sed.ui.visualization.execution_tree.wizard.CreateDebugNodeWizard.CreateDebugNodeWizardResult;

/**
 * Implementation of {@link ICreateFeature} for {@link ISEDExceptionalTermination}s.
 * @author Martin Hentschel
 */
public class ExceptionalTerminationCreateFeature extends AbstractDebugNodeCreateFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public ExceptionalTerminationCreateFeature(IFeatureProvider fp) {
       super(fp, "Exceptional Termination", "Create a new Exceptional Termination");
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getCreateImageId() {
      return IExecutionTreeImageConstants.IMG_EXCEPTIONAL_TERMINATION;
   }

   /**
    * {@inheritDoc}
    */   
   @Override
   public String getNodeType() {
      return "Exceptional Termination";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ISEDDebugNode createNewDebugNode(CreateDebugNodeWizardResult initialValues) throws DebugException {
      ISEDDebugNode parent = initialValues.getParent();
      Assert.isNotNull(parent);
      SEDMemoryExceptionalTermination result = new SEDMemoryExceptionalTermination(parent.getDebugTarget(), parent, parent.getThread());
      result.setName(initialValues.getName());
      return result;
   }

}