package org.key_project.jmlediting.core.profile;

import org.eclipse.core.resources.IProject;

/**
 * A listener to listen to changes to the JML profiles of a project.
 *
 * @author Moritz Lichter
 *
 */
public interface IProjectProfileListener {

   /**
    * The profile of the current project has changed.
    *
    * @param project
    *           the porject those profile changed
    * @param newProfile
    *           the new current profile
    */
   void profileChanged(IProject project, IJMLProfile newProfile);

}
