package org.key_project.key4eclipse.starter.ui.starter;

import org.eclipse.core.resources.IProject;
import org.key_project.key4eclipse.common.ui.starter.IProjectStarter;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;

/**
 * Starts a proof in the original user interface of KeY.
 * @author Martin Hentschel
 */
public class KeYProjectStarter implements IProjectStarter {
   /**
    * {@inheritDoc}
    */
   @Override
   public void open(IProject project) throws Exception {
      KeYUtil.loadAsync(project);
   }
}
