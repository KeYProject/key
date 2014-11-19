package org.key_project.jmlediting.core.profile;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.key_project.jmlediting.core.Activator;
import org.key_project.jmlediting.core.PropertyNames;

/**
 * 
 * The {@link JMLPreferencesHelper} helps to set preferences and properties.
 * @author Moritz Lichter
 *
 */
public final class JMLPreferencesHelper {
   
   /**
    * No instantiations.
    */
   private JMLPreferencesHelper() {
      
   }

   /**
    * Returns the default profile from the eclipse preferences or null.
    * 
    * @return the default profile or null if not set
    */
   public static IJMLProfile getDefaultJMLProfile() {
      String currentProfileIdentifier;
      IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      currentProfileIdentifier = preferences.get(
            PropertyNames.DEFAULT_JML_PROFILE, null);
      if (currentProfileIdentifier == null) {
         return null;
      }
      return JMLProfileManagement
            .getProfileFromIdentifier(currentProfileIdentifier);
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
      IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      // global properties
      preferences.put(PropertyNames.DEFAULT_JML_PROFILE,
            profile.getIdentifier());
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
      catch (CoreException e) {
         return null;
      }
      return JMLProfileManagement.getProfileFromIdentifier(currentProfileName);
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
    * @param project the project to set for
    * @param profile the profile to set or null
    * @throws CoreException when problem storing properties
    */
   public static void setProjectJMLProfile(final IProject project, final IJMLProfile profile)
         throws CoreException {
      String profileIdentifier = null;
      if (profile != null) {
         profileIdentifier = profile.getIdentifier();
      }
      project.setPersistentProperty(PropertyNames.PROFILE, profileIdentifier);
   }

}
