package org.key_project.key4eclipse.common.ui.starter;

import org.eclipse.core.resources.IFile;

/**
 * Instances of this class are used to start an application
 * and to load the given {@link IFile} in it.
 * @author Martin Hentschel
 */
public interface IFileStarter {
   /**
    * Open the application.
    * @param file The {@link IFile} to load.
    * @throws Exception Occurred Exception.
    */
   public void open(IFile file) throws Exception;
}
