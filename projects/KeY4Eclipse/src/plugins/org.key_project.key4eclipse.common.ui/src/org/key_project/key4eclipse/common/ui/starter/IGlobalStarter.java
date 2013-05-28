package org.key_project.key4eclipse.common.ui.starter;

/**
 * Instances of this class are used to start an application without
 * loading any specific content.
 * @author Martin Hentschel
 */
public interface IGlobalStarter {
   /**
    * Open the application.
    * @throws Exception Occurred Exception.
    */
   public void open() throws Exception;
}
