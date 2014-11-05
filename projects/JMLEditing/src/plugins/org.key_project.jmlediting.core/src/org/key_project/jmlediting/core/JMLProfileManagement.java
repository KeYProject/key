package org.key_project.jmlediting.core;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.Platform;

/**
 * This class helps managing the available JML profiles.
 * 
 * @author Moritz Lichter
 *
 */
public final class JMLProfileManagement {

   /**
    * Private constructor to prohibit creating objects of this class.
    */
   private JMLProfileManagement() {

   }

   /**
    * A map implementing a cache for the profile objects. The cache caches the
    * created object for class names of the configuration. The cache also
    * ensures that only one profile objects exists for a class.
    */
   private static Map<String, IJMLProfile> profileCache = new HashMap<String, IJMLProfile>();

   /**
    * Returns a set of all JML profiles which are available. The set may be
    * empty.
    * 
    * @return a unmodifiable set of the current JML profiles
    */
   public static Set<IJMLProfile> getAvailableProfiles() {
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
            String profileClass = elem.getAttribute("class");
            // Try to read cahe
            IJMLProfile profile = getProfileFromClassName(profileClass);
            if (profile == null) {
               try {
                  Object profileO = elem.createExecutableExtension("class");
                  if (profileO instanceof IJMLProfile) {
                     profile = (IJMLProfile) profileO;
                     profileCache.put(profileClass, profile);
                  }
               }
               catch (CoreException e) {
                  // TODO Auto-generated catch block
                  e.printStackTrace();
               }
            }
            if (profile != null) {
               availableProfiles.add(profile);
            }
         }
      }

      return Collections.unmodifiableSet(availableProfiles);
   }

   public static List<IJMLProfile> getAvailableProfilesSortedByName() {
      List<IJMLProfile> profiles = new ArrayList<IJMLProfile>(
            getAvailableProfiles());
      Collections.sort(profiles, new Comparator<IJMLProfile>() {

         @Override
         public int compare(final IJMLProfile o1, final IJMLProfile o2) {
            return o1.getName().compareTo(o2.getName());
         }
      });
      return profiles;
   }

   public static IJMLProfile getProfileFromClassName(String className) {
      IJMLProfile profile = profileCache.get(className);
      return profile;
   }

}
