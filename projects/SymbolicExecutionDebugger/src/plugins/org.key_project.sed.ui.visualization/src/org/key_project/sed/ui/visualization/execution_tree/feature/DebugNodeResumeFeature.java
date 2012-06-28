package org.key_project.sed.ui.visualization.execution_tree.feature;

import org.eclipse.debug.core.commands.IDebugCommandHandler;
import org.eclipse.debug.core.model.ISuspendResume;
import org.eclipse.debug.internal.core.commands.ResumeCommand;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.custom.ICustomFeature;

/**
 * An {@link ICustomFeature} which executes {@link ISuspendResume#resume()}
 * on selected business objects.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class DebugNodeResumeFeature extends AbstractDebugNodeSuspendResumeFeature {
   /**
    * Constructor.
    * @param fp The {@link IFeatureProvider} to use.
    */
   public DebugNodeResumeFeature(IFeatureProvider fp) {
      super(fp);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean canExecute(ISuspendResume suspendResume) {
      return suspendResume.canResume();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IDebugCommandHandler createCommand() {
      return new ResumeCommand();
   }
}
