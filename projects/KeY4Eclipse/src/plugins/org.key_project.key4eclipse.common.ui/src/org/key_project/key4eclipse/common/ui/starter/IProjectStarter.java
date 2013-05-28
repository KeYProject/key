package org.key_project.key4eclipse.common.ui.starter;

import org.eclipse.core.resources.IProject;

/**
 * Instances of this class are used to start an application
 * and to load the given {@link IProject} in it.
 * @author Martin Hentschel
 */
public interface IProjectStarter {
   /**
    * Open the application.
    * @param project The {@link IProject} to load.
    * @throws Exception Occurred Exception.
    */
   public void open(IProject project) throws Exception;
}
