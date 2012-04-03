package org.key_project.sed.ui.visualization.execution_tree.feature;

import java.util.List;

import org.eclipse.graphiti.features.IAddFeature;
import org.eclipse.graphiti.features.ICreateFeature;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.memory.SEDMemoryDebugTarget;
import org.key_project.sed.core.model.memory.SEDMemoryThread;
import org.key_project.sed.ui.visualization.execution_tree.provider.IExecutionTreeImageConstants;
import org.key_project.sed.ui.visualization.execution_tree.wizard.CreateDebugNodeWizard.CreateDebugNodeWizardResult;

/**
 * Implementation of {@link ICreateFeature} for {@link ISEDThread}s.
 * @author Martin Hentschel
 */
public class ThreadCreateFeature extends AbstractDebugNodeCreateFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} which provides this {@link IAddFeature}.
    */
   public ThreadCreateFeature(IFeatureProvider fp) {
       super(fp, "Thread", "Create a new Thread");
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getCreateImageId() {
      return IExecutionTreeImageConstants.IMG_THREAD;
   }
   
   /**
    * {@inheritDoc}
    */   
   @Override
   public String getNodeType() {
      return "Thread";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected List<ISEDDebugNode> collectExistingNodes() {
      return null; // Return null to indicate that no parent is required.
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ISEDDebugNode createNewDebugNode(CreateDebugNodeWizardResult initialValues) {
      // Create debug target
      SEDMemoryDebugTarget target = new SEDMemoryDebugTarget(null);
      // Create thread
      SEDMemoryThread result = new SEDMemoryThread(target);
      result.setName(initialValues.getName());
      return result;
   }
}