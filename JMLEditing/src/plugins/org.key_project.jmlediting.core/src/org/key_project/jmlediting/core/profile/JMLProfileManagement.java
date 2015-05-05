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
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.key_project.jmlediting.core.Activator;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceException;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceFactory;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.osgi.service.prefs.BackingStoreException;
import org.osgi.service.prefs.Preferences;

/**
 * This class helps managing the available JML profiles.
 *
 * @author Moritz Lichter
 *
 */
public final class JMLProfileManagement {

   /**
    * Constant node name for preferences.
    */
   private static final String JML_DERIVED_PROFILES = "JMLDerivedProfiles";

   /**
    * Shared instance.
    */
   private static final JMLProfileManagement INSTANCE = new JMLProfileManagement();

   /**
    * Returns the default instance of the {@link JMLProfileManagement}.
    *
    * @return the shared instance.
    */
   public static JMLProfileManagement instance() {
      return INSTANCE;
   }

   /**
    * A map implementing a cache for the profile objects. The cache caches the
    * created object by identifier. The cache also ensures that only one profile
    * objects exists for an identifier.
    */
   private final Map<String, IJMLProfile> profileCache = new HashMap<String, IJMLProfile>();
   /**
    * Stores all user defined profiles from the eclipse settings, thus a subset
    * of the value set of the profileCache.
    */
   private final Set<IDerivedProfile> userDefinedProfiles = new HashSet<IDerivedProfile>();

   /**
    * List for all listeners.
    */
   private final List<IProfileManagementListener> listeners;

   /**
    * Private constructor to prohibit creating objects of this class.
    */
   private JMLProfileManagement() {
      this.listeners = new ArrayList<IProfileManagementListener>();
   }

   /**
    * Adds the given listener.
    *
    * @param listener
    *           the new listener, not allowed to be null
    */
   public void addListener(final IProfileManagementListener listener) {
      this.listeners.add(listener);
   }

   /**
    * Removed the given listener.
    *
    * @param listener
    *           the listener to remove
    */
   public void removeListener(final IProfileManagementListener listener) {
      this.listeners.remove(listener);
   }

   /**
    * Fires a new profile added event to all listeners.
    *
    * @param newProfile
    *           the new profile
    */
   private void fireNewProfileAddedEvent(final IJMLProfile newProfile) {
      for (final IProfileManagementListener listener : this.listeners) {
         listener.newProfileAdded(newProfile);
      }
   }

   /**
    * Returns a set of all JML profiles which are available. The set may be
    * empty.
    *
    * @return a unmodifiable set of the current JML profiles
    */
   public Set<IJMLProfile> getAvailableProfiles() {
      try {
         // First load profiles from extension points
         this.loadExtensionProfiles();
         // Then load the derived ones, because they need access to them of the
         // extenion points
         this.loadDerivedProfiles();
      }
      catch (final InvalidProfileException e) {
         throw new RuntimeException(e);
      }
      // No all profiles are in the cache
      return Collections.unmodifiableSet(new HashSet<IJMLProfile>(
            this.profileCache.values()));
   }

   /**
    * Stores the given profile in the cache if a profile with its identifier is
    * not already known. The profile is validated before caching.
    *
    * @param profile
    *           the profile to store in the cache
    * @return whether the profile was stored in the cache because it was new
    * @throws InvalidProfileException
    *            if the profile is not valid
    */
   private boolean cacheProfile(final IJMLProfile profile)
         throws InvalidProfileException {
      if (!this.profileCache.containsKey(profile.getIdentifier())) {
         this.validateProfile(profile);
         this.profileCache.put(profile.getIdentifier(), profile);
         return true;
      }
      else {
         // An object for this identifier has already been created
         // reuse it from the cache and throw away the created one
         return false;
      }
   }

   /**
    * Stores the given profile in the cache and remembers it as a user defined
    * profile.
    *
    * @param profile
    *           the profile to cache
    * @throws InvalidProfileException
    *            if the profile is invalid and cannot be used
    */
   private void cacheUserDefinedProfile(final IDerivedProfile profile)
         throws InvalidProfileException {
      if (this.cacheProfile(profile)) {
         this.userDefinedProfiles.add(profile);
      }
   }

   /**
    * Loads all available profiles from registered extension points and puts
    * them into the cache.
    *
    * @throws InvalidProfileException
    *            if any profile is not valid
    */
   private void loadExtensionProfiles() throws InvalidProfileException {
      // Get the extension point
      final IExtensionPoint extensionPoint = Platform.getExtensionRegistry()
            .getExtensionPoint("org.key_project.jmlediting.core.profiles");

      // Now check all provided extension points
      for (final IExtension extension : extensionPoint.getExtensions()) {
         for (final IConfigurationElement elem : extension
               .getConfigurationElements()) {
            try {
               final Object profileO = elem.createExecutableExtension("class");
               if (profileO instanceof IJMLProfile) {
                  this.cacheProfile((IJMLProfile) profileO);
               }
               else {
                  throw new InvalidProfileException(
                        "Registered profile does not implement IJMLProfile.");
               }
            }
            catch (final CoreException e) {
               // Invalid class of the extension object
               throw new InvalidProfileException(
                     "Got invalid extension object", e);
            }

         }
      }
   }

   /**
    * Loads all user defined derived profiles in the current workspace settings
    * and puts them into the cache.
    *
    * @throws InvalidProfileException
    *            if any profile is invalid
    */
   private void loadDerivedProfiles() throws InvalidProfileException {
      final IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      final Preferences p = preferences.node(JML_DERIVED_PROFILES);
      try {
         final String[] profileKeys = p.keys();
         for (final String profileKey : profileKeys) {
            // Check whether this profile is not already known, otherwise we can
            // skip parsing and loading it
            if (!this.profileCache.containsKey(profileKey)) {

               // Get the XML string from the preferences
               final String xmlContent = p.get(profileKey, null);
               if (xmlContent == null) {
                  throw new InvalidProfileException("Profile with id "
                        + profileKey + " not found");
               }

               try {
                  // Parse the profile

                  // and load the profile
                  final IDerivedProfile profile = ProfilePersistenceFactory
                        .createDerivedProfilePersistence().read(xmlContent);
                  // Check that the profile has the same id as the preference
                  // key
                  if (!profile.getIdentifier().equals(profileKey)) {
                     throw new InvalidProfileException(
                           "Profile has a wrong id. Expected " + profileKey
                                 + " but got " + profile.getIdentifier());
                  }
                  // Remember the user defined profiles because they need to be
                  // written back eventually
                  this.cacheUserDefinedProfile(profile);

               }
               catch (final ProfilePersistenceException e) {
                  throw new InvalidProfileException(
                        "Could not read the profile for id " + profileKey, e);
               }
            }
         }
      }
      catch (final BackingStoreException e) {
         throw new InvalidProfileException(
               "Failed to access the eclipse preferences", e);
      }
   }

   /**
    * Writes all user defined profiles back to the workspace settings to persist
    * them between different runtimes. This only writes the derived profiles,
    * which are user defined and not supplied by an extension point.
    *
    * @throws InvalidProfileException
    *            if any profile is invalid and thus cannot be persisted
    */
   public void writeDerivedProfiles() throws InvalidProfileException {
      final IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      final Preferences p = preferences.node(JML_DERIVED_PROFILES);
      try {
         p.clear();
      }
      catch (final BackingStoreException e1) {
         throw new InvalidProfileException(e1);
      }
      for (final IDerivedProfile profile : this.userDefinedProfiles) {

         try {
            // Create the XML Document and convert it to a string
            final String document = ProfilePersistenceFactory
                  .createDerivedProfilePersistence().persist(profile);
            // Put the string in the prferences
            p.put(profile.getIdentifier(), document);
         }
         catch (final ProfilePersistenceException e) {
            throw new InvalidProfileException(
                  "Unable to persist the given profile", e);
         }
      }
   }

   /**
    * Adds a new user defined profile to the available profiles. The profile is
    * written to the eclipse preferences immediately.
    *
    * @param newProfile
    *           the new user defined profile
    * @throws InvalidProfileException
    *            is the user profile is invalid and cannot be used.
    */
   public void addUserDefinedProfile(final IDerivedProfile newProfile)
         throws InvalidProfileException {
      if (this.getProfileFromIdentifier(newProfile.getIdentifier()) != null) {
         throw new InvalidProfileException(
               "A profile with the given id is already known.");
      }
      this.cacheUserDefinedProfile(newProfile);
      this.writeDerivedProfiles();
      this.fireNewProfileAddedEvent(newProfile);
   }

   public boolean isUserDefinedProfile(final IDerivedProfile profile) {
      return this.userDefinedProfiles.contains(profile);
   }

   public void removeUserDefinedProfile(final IDerivedProfile profile)
         throws InvalidProfileException {
      this.userDefinedProfiles.remove(profile);
      this.profileCache.remove(profile.getIdentifier());
      this.writeDerivedProfiles();
   }

   /**
    * Does some validations on the given profile to catch exceptions early on
    * not on runtime later. If validation is not successful, this method throws
    * an exception.
    *
    * @param profile
    *           the profile to validate
    * @throws InvalidProfileException
    *            if the validation failed because the profile is invalid
    */
   private void validateProfile(final IJMLProfile profile)
         throws InvalidProfileException {
      // Do some validations on the profile:
      try {
         for (final IKeyword keywort : profile.getSupportedKeywords()) {
            if (keywort.getSort() != null) {
               AbstractKeywordSort.validateContentOfInstanceField(keywort
                     .getSort());
            }
         }
      }
      catch (final Exception e) {
         throw new InvalidProfileException("Failed to validate the profile "
               + profile.getName(), e);
      }
   }

   /**
    * Returns all available JML profiles sorted by their names.
    *
    * @return the sorted list of profiles
    */
   public List<IJMLProfile> getAvailableProfilesSortedByName() {
      final List<IJMLProfile> profiles = new ArrayList<IJMLProfile>(
            this.getAvailableProfiles());
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
   public IJMLProfile getProfileFromIdentifier(final String identifier) {
      IJMLProfile profile = this.profileCache.get(identifier);
      if (profile == null) {
         // Maybe the user did not call getAvailableProfiles, so the cache is
         // not filled up
         // Try this
         this.getAvailableProfiles();
         profile = this.profileCache.get(identifier);
      }
      return profile;
   }

   /**
    * Returns the IJMLProfile for the given name or null if no profile is found
    * for the name.
    *
    * @param name
    *           the name of the profile
    * @return the profile or null
    */
   public IJMLProfile getProfileFromName(final String name) {
      for (final IJMLProfile profile : this.getAvailableProfiles()) {
         if (profile.getName().equals(name)) {
            return profile;
         }
      }
      return null;
   }
}
