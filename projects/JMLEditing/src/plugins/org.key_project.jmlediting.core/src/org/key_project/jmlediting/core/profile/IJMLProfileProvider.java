package org.key_project.jmlediting.core.profile;

import org.eclipse.core.runtime.CoreException;

/**
 * The {@link IJMLProfileProvider} can be used to provide JML profiles without
 * having created the object by now. Instead, an instance of this interface is
 * provided which is then asked to create the profile. This can be used e.g. to
 * load the profile from a file. The provider needs to define a meaningful
 * equals implementation. As long objects will provide an instance of the same
 * profile, the need to be equal for good caching.
 * 
 * @author Moritz Lichter
 *
 */
public interface IJMLProfileProvider {

   /**
    * Provides the jml profile. This method is called only once if the equal
    * method of this provider guarantees that two provider objects are equal if
    * they provide the same profile.
    * 
    * @return the profile to provide
    * @throws CoreException
    *            if creating the profiles causes trouble
    */
   IJMLProfile provideProfile() throws CoreException;

}
