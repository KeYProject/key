package org.key_project.jmlediting.core.test.profile;

import static org.junit.Assert.assertTrue;

import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.core.test.TestUtils;

public class JMLPreferencesHelperTest {

   private static List<IJMLProfile> profiles;
   private static IJMLProfile workspaceProfile;

   @BeforeClass
   public static void initializeProfiles() {
      profiles = JMLProfileManagement.getAvailableProfilesSortedByName();
   }

   @BeforeClass
   public static void saveWorkspaceProfile() {
      workspaceProfile = JMLPreferencesHelper.getDefaultJMLProfile();
   }

   @AfterClass
   public static void restoreWorkspaceProfile() {
      JMLPreferencesHelper.setDefaultJMLProfile(workspaceProfile);
   }

   @Test
   public void testSetDefaultProfile() {
      assertTrue("No default profile returned but some was available",
            JMLPreferencesHelper.getDefaultJMLProfile() != null);
      IJMLProfile defaultProf = profiles.get(0);
      JMLPreferencesHelper.setDefaultJMLProfile(defaultProf);
      assertTrue("Default profile is not correct",
            JMLPreferencesHelper.getDefaultJMLProfile() == defaultProf);
      defaultProf = profiles.get(1);
      JMLPreferencesHelper.setDefaultJMLProfile(defaultProf);
      assertTrue("Default profile is not correct after changing",
            JMLPreferencesHelper.getDefaultJMLProfile() == defaultProf);
   }

   @Test(expected = NullPointerException.class)
   public void testSetNullDefaultProfile() {
      JMLPreferencesHelper.setDefaultJMLProfile(null);
   }

   @Test
   public void testSetProjectProfile() throws CoreException {
      final IProject project = TestUtils.createJavaProject("Test");
      assertTrue("New profile has no project specific profile",
            !JMLPreferencesHelper.hasProjectJMLProfile(project));
      assertTrue("getProjectJMLProfile returns not null when no profile set",
            JMLPreferencesHelper.getProjectJMLProfile(project) == null);

      IJMLProfile profile = profiles.get(0);
      JMLPreferencesHelper.setProjectJMLProfile(project, profile);
      assertTrue("Project has no profile but it has been set",
            JMLPreferencesHelper.hasProjectJMLProfile(project));
      assertTrue("Wrong profile returned for project",
            JMLPreferencesHelper.getProjectJMLProfile(project) == profile);

      profile = profiles.get(1);
      JMLPreferencesHelper.setProjectJMLProfile(project, profile);
      assertTrue("Wrong profile returned for project",
            JMLPreferencesHelper.getProjectJMLProfile(project) == profile);

      JMLPreferencesHelper.setProjectJMLProfile(project, null);
      assertTrue("Project has profile but it has been cleared",
            !JMLPreferencesHelper.hasProjectJMLProfile(project));
      assertTrue("getProjectJMLProfile returns not null when no profile set",
            JMLPreferencesHelper.getProjectJMLProfile(project) == null);
   }

}
