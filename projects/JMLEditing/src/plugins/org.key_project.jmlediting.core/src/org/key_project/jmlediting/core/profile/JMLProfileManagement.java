package org.key_project.jmlediting.core.profile;

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
    * created object by identifier. The cache also ensures that only one profile
    * objects exists for an identifier.
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

            try {
               Object profileO = elem.createExecutableExtension("class");
               if (profileO instanceof IJMLProfile) {
                  IJMLProfile profile = (IJMLProfile) profileO;
                  if (!profileCache.containsKey(profile.getIdentifier())) {
                     profileCache.put(profile.getIdentifier(), profile);
                     availableProfiles.add(profile);
                  } else {
                     // An object for this identifier has already been created
                     // reuse it from the cache and throw away the created one
                     availableProfiles.add(profileCache.get(profile.getIdentifier()));
                  }
               }

            }
            catch (CoreException e) {
               // Ignore this invalid extension
            }

         }
      }

      return Collections.unmodifiableSet(availableProfiles);
   }

   /**
    * Returns all available JML profiles sorted by their names.
    * 
    * @return the sorted list of profiles
    */
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

   /**
    * Returns the IJMLProfile for the given identifier or null if no profile is
    * found for the identifier.
    * 
    * @param identifier
    *           the identifer of the profile
    * @return the profile or null
    */
   public static IJMLProfile getProfileFromIdentifier(final String identifier) {
      IJMLProfile profile = profileCache.get(identifier);
      if (profile == null) {
         // Maybe the user did not call getAvailableProfiles, so the cache is
         // not filled up
         // Try this
         getAvailableProfiles();
         profile = profileCache.get(identifier);
      }
      return profile;
   }

}
