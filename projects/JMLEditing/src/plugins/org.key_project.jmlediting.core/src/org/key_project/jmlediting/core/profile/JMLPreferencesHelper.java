package org.key_project.jmlediting.core.profile;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.key_project.jmlediting.core.Activator;
import org.key_project.jmlediting.core.PropertyNames;

public class JMLPreferencesHelper {

   public static IJMLProfile getDefaultJMLProfile() {
      String currentProfileName;
      IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      currentProfileName = preferences.get(
            PropertyNames.DEFAULT_JML_PROFILE, null);
      return JMLProfileManagement.getProfileFromClassName(currentProfileName);
   }

   public static IJMLProfile getProjectJMLProfile(final IProject project) {
      String currentProfileName;
      try {
         currentProfileName =project.getPersistentProperty(
               PropertyNames.PROFILE);
      }
      catch (CoreException e) {
         currentProfileName = null;
      }
      return JMLProfileManagement.getProfileFromClassName(currentProfileName);
   }
   
   public static boolean hasProjectJMLProfile(final IProject project) {
      return getProjectJMLProfile(project) != null;
   }

   public static void setProjectJMLProfile(
         IProject project, IJMLProfile profile) throws CoreException {
      String profileClassName = null;
      if (profile != null) {
         profileClassName = profile.getClass().getName();
      }
      project.setPersistentProperty(PropertyNames.PROFILE,
            profileClassName);
   }

   public  static void setDefaultJMLProfile(IJMLProfile profile) {
      if (profile == null) {
         throw new NullPointerException("Cannot set a null default profile");
      }
      IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      // global properties
      preferences
            .put(PropertyNames.DEFAULT_JML_PROFILE, profile.getClass().getName());
   }

}
