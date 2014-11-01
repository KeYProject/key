package org.key_project.jmlediting.core;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;

/**
 * This class helps managing the available JML profiles.
 * 
 * @author Moritz Lichter
 *
 */
public class JMLProfileManagement {

   /**
    * Returns a set of all JML profiles which are available. The set may be
    * empty.
    * 
    * @return a unmodifiable set of the current JML profiles
    * @throws CoreException
    *            if there is a problem converting registered profiles
    */
   public static Set<IJMLProfile> getAvailableProfiles() throws CoreException {
      Set<IJMLProfile> availableProfiles = new HashSet<IJMLProfile>();

      // Get the extension point
      IExtensionPoint extensionPoint = Platform.getExtensionRegistry()
            .getExtensionPoint("org.key_project.jmlediting.core.profiles");

      if (extensionPoint == null) {
         return Collections.emptySet();
      }

      // Now check all provided extension points
      for (IExtension extension : extensionPoint.getExtensions()) {
         for (IConfigurationElement elem : extension.getConfigurationElements()) {
            // Get the object and check its class
            Object o = elem.createExecutableExtension("class");
            if (o instanceof IJMLProfile) {
               availableProfiles.add((IJMLProfile) o);
            }
            else {
               // wrong class, throw an exception
               throw new CoreException(new Status(Status.ERROR,
                     Activator.PLUGIN_ID,
                     "Got jml profile object which does not implement IJMLProfile:"
                           + o));
            }
         }
      }

      return Collections.unmodifiableSet(availableProfiles);
   }

}
