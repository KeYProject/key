package org.key_project.jmlediting.core.profile;

import org.eclipse.core.runtime.CoreException;

public interface IJMLProfileProvider {
   
   public IJMLProfile provideProfile() throws CoreException;

}
