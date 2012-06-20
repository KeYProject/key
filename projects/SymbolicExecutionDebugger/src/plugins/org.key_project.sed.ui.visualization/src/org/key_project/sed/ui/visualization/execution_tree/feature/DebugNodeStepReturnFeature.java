package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.debug.core.commands.IDebugCommandHandler;
import org.eclipse.debug.core.model.IStep;
import org.eclipse.debug.internal.core.commands.StepReturnCommand;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.custom.ICustomFeature;

/**
 * An {@link ICustomFeature} which executes {@link IStep#stepReturn()}
 * on selected business objects.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class DebugNodeStepReturnFeature extends AbstractDebugNodeStepFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} to use.
    */
   public DebugNodeStepReturnFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean canExecute(IStep step) {
      return step.canStepReturn();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IDebugCommandHandler createCommand() {
      return new StepReturnCommand();
   }
}
