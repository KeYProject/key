package org.key_project.key4eclipse.common.ui.starter;

import org.eclipse.jdt.core.IMethod;

/**
 * Instances of this class are used to start an application
 * and to load the given {@link IMethod} in it.
 * @author Martin Hentschel
 */
public interface IMethodStarter {
   /**
    * Open the application.
    * @param method The {@link IMethod} to load.
    * @throws Exception Occurred Exception.
    */
   public void open(IMethod method) throws Exception;
}
