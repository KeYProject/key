package org.key_project.jmlediting.core.profile;

import java.util.ArrayList;
import java.util.List;
import java.util.NoSuchElementException;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IEclipsePreferences.IPreferenceChangeListener;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.key_project.javaeditor.util.PreferenceUtil;
import org.key_project.jmlediting.core.Activator;
import org.key_project.jmlediting.core.PropertyNames;

/**
 *
 * The {@link JMLPreferencesHelper} helps to set preferences and properties.
 *
 * @author Moritz Lichter
 *
 */
public final class JMLPreferencesHelper {
   /**
    * The ID of the JML Java Editor extension.
    */
   public static final String JML_EDITOR_EXTENSION_ID = "org.key_project.jmlediting.ui.extension.JMLSourceViewerConfigurationExtension";

   /**
    * The ID of the default profile.
    */
   private static final String DEFAULT_PROFILE_IDENTIFIER = "org.key_project.jmlediting.profile.key";

   /**
    * List of associated listener.
    */
   private static List<IProjectProfileListener> projectListener = new ArrayList<IProjectProfileListener>();

   /**
    * No instantiations.
    */
   private JMLPreferencesHelper() {

   }

   /**
    * Returns true, if any JML profile is available. Iff this method returns
    * true, the following methods are guaranteed to return a non null JML
    * Profile: {@link JMLPreferencesHelper#getDefaultJMLProfile()},
    * {@link JMLPreferencesHelper#getProjectActiveJMLProfile(IProject)}.
    *
    * @return whether any JML Profile is available
    */
   public static boolean isAnyProfileAvailable() {
      return getDefaultJMLProfile() != null;
   }

   /**
    * Returns the default default profile.
    * @return The default default profile.
    */
   public static IJMLProfile getDefaultDefaultJMLProfile() {
      return JMLProfileManagement.instance().getProfileFromIdentifier(DEFAULT_PROFILE_IDENTIFIER);
   }

   /**
    * Returns the default profile from the eclipse preferences. If no profile is
    * set for the workspace, this methods tries to set the JML Reference
    * profile, if not found, it takes the first one. If there is no profile
    * available, it throws an {@link NoSuchElementException}.
    *
    * @return the default profile
    */
   public static IJMLProfile getDefaultJMLProfile() {
      String currentProfileIdentifier;
      final IEclipsePreferences preferences = InstanceScope.INSTANCE.getNode(Activator.PLUGIN_ID);
      currentProfileIdentifier = preferences.get(PropertyNames.DEFAULT_JML_PROFILE, null);
      if (currentProfileIdentifier == null) {
         // No workspace default is set
         // Try to find the reference profile, it is not required to be
         // installed
         IJMLProfile profile = null;
         final List<IJMLProfile> allProfiles = JMLProfileManagement.instance().getAvailableProfilesSortedByName();
         if (allProfiles.isEmpty()) {
            throw new NoSuchElementException("No JML Profile installed!");
         }
         for (final IJMLProfile p : allProfiles) {
            if (p.getIdentifier().equals(DEFAULT_PROFILE_IDENTIFIER)) {
               profile = p;
            }
         }
         // Otherwise just use the first one
         if (profile == null) {
            profile = allProfiles.get(0);
         }
         // Set the picked profile as default
         setDefaultJMLProfile(profile);
         return profile;
      }
      return JMLProfileManagement.instance().getProfileFromIdentifier(currentProfileIdentifier);
   }

   /**
    * Sets the default profile for the eclipse workspace.
    *
    * @param profile
    *           the profile to set
    */
   public static void setDefaultJMLProfile(final IJMLProfile profile) {
      if (profile == null) {
         throw new NullPointerException("Cannot set a null default profile");
      }
      final IEclipsePreferences preferences = InstanceScope.INSTANCE.getNode(Activator.PLUGIN_ID);
      // global properties
      preferences.put(PropertyNames.DEFAULT_JML_PROFILE, profile.getIdentifier());
   }

   /**
    * Returns the JML profile which has been set to the project as project
    * specific profile. It a specific profile is not set, this method returns
    * null.
    *
    * @param project
    *           the project to get the profile for
    * @return the project specific profile or null
    */
   public static IJMLProfile getProjectJMLProfile(final IProject project) {
      String currentProfileName;
      try {
         currentProfileName = project
               .getPersistentProperty(PropertyNames.PROFILE);
      }
      catch (final CoreException e) {
         return null;
      }
      return JMLProfileManagement.instance().getProfileFromIdentifier(
            currentProfileName);
   }

   /**
    * Returns whether the given profile has a project specific JML profile set.
    *
    * @param project
    *           the project to ask for
    * @return true iff the project contains a project specific JML profile
    */
   public static boolean hasProjectJMLProfile(final IProject project) {
      return getProjectJMLProfile(project) != null;
   }

   /**
    * Sets the given JML profile as project specific for the given project. Set
    * a null profile to remove project specific settings.
    *
    * @param project
    *           the project to set for
    * @param profile
    *           the profile to set or null
    * @throws CoreException
    *            when problem storing properties
    */
   public static void setProjectJMLProfile(final IProject project,
         final IJMLProfile profile) throws CoreException {
      String profileIdentifier = null;
      if (profile != null) {
         profileIdentifier = profile.getIdentifier();
      }
      project.setPersistentProperty(PropertyNames.PROFILE, profileIdentifier);

      for (final IProjectProfileListener profileListener : projectListener) {
         profileListener.profileChanged(project, profile);
      }
   }

   /**
    * Adds a {@link IProjectProfileListener} to the preferences management.
    *
    * @param listener
    *           the new listener, not allowed to be null
    */
   public static void addProjectProfileListener(
         final IProjectProfileListener listener) {
      if (listener == null) {
         throw new IllegalArgumentException(
               "listener is not allowed to be null");
      }
      projectListener.add(listener);
   }

   /**
    * Removes the given {@link IProjectProfileListener} from the preferences
    * management.
    *
    * @param listener
    *           the listener to remove
    */
   public static void removeProjectProfileListener(
         final IProjectProfileListener listener) {
      projectListener.remove(listener);
   }

   /**
    * Removes the given listener which listens to changes of the default
    * profile.
    *
    * @param listener
    *           the listener to remove
    */
   public static void removeDefaultProfilePreferencesListener(
         final IPreferenceChangeListener listener) {
      InstanceScope.INSTANCE.getNode(Activator.PLUGIN_ID)
            .removePreferenceChangeListener(listener);
   }

   /**
    * Returns the JML profile which has been set to the project as project
    * specific profile. It a specific profile is not set, this method returns
    * the default one.
    *
    * @param project
    *           the project to get the profile for
    * @return the project specific profile or the default
    */
   public static IJMLProfile getProjectActiveJMLProfile(final IProject project) {
      IJMLProfile result = getProjectJMLProfile(project);

      if (result == null) {
         result = getDefaultJMLProfile();
      }
      return result;
   }

   /**
    * Returns whether JML Editing is enabled. True is the default
    *
    * @return whether JML Editing is enabled
    */
   public static boolean isExtensionEnabled() {
      return PreferenceUtil.isExtensionsEnabled() &&
             PreferenceUtil.isExtensionEnabled(JML_EDITOR_EXTENSION_ID);
   }
}
