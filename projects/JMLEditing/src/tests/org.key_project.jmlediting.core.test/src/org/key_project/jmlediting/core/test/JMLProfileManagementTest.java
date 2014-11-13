package org.key_project.jmlediting.core.test;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.Set;

import org.eclipse.core.runtime.CoreException;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;

public class JMLProfileManagementTest {

   public static class DummyJMLProfile1 implements IJMLProfile {

      @Override
      public String getName() {
         return "DummyJMLProfile1";
      }

   }

   public static class DummyJMLProfile2 implements IJMLProfile {

      @Override
      public String getName() {
         return "DummyJMLProfile2";
      }

   }

   @Test
   public void test() {
      Set<IJMLProfile> availablesProfiles = JMLProfileManagement
            .getAvailableProfiles();
      assertTrue(
            "Found no available profiles " + availablesProfiles.getClass(),
            !availablesProfiles.isEmpty());

      boolean containsDummy1 = false;
      boolean containsDummy2 = false;
      for (IJMLProfile profile : availablesProfiles) {
         if (profile.getName().equals("DummyJMLProfile1")) {
            containsDummy1 = true;
         }
         if (profile.getName().equals("DummyJMLProfile2")) {
            containsDummy2 = true;
         }
      }

      assertTrue("Dummy Profiles are not included", containsDummy1
            && containsDummy2);

   }

}
