package org.key_project.util.eclipse.setup;

/**
 * Instances of this class are registered via extension point
 * {@value SetupStartup#SETUP_PARTICIPANTS_EXTENSION_POINT} and allows
 * to initialize a fresh workspace once or on each startup.
 * @author Martin Hentschel
 */
public interface ISetupParticipant {
   /**
    * Returns a unique ID of this {@link ISetupParticipant}.
    * @return
    */
   public String getID();
   
   /**
    * Initializes the workspace when it is used the first with the
    * plug-in which provides this {@link ISetupParticipant}.
    */
   public void setupWorkspace();

   /**
    * Initializes the workspace on each program start.
    */
   public void startup();
}
