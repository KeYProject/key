package org.key_project.jmlediting.core.test.profile;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.Set;

import org.eclipse.core.runtime.CoreException;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.ConfigurableJMLProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.IJMLProfileProvider;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;

public class JMLProfileManagementTest {

   public static class DummyJMLProfile1 extends ConfigurableJMLProfile {

      public DummyJMLProfile1() {
         super( "DummyJMLProfile1",DummyJMLProfile1.class.getName());
      }

   }

   public static class DummyJMLProfile2 extends ConfigurableJMLProfile {

      public DummyJMLProfile2() {
         super( "DummyJMLProfile2",DummyJMLProfile2.class.getName());
      }

   }
   
   public static class DummyJMLProfile3Provider implements IJMLProfileProvider {

      @Override
      public IJMLProfile provideProfile() throws CoreException {
         return new ConfigurableJMLProfile("DummyJMLProfile3", DummyJMLProfile3Provider.class.getName());
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
      boolean containsDummy3 = false;
      for (IJMLProfile profile : availablesProfiles) {
         if (profile.getName().equals("DummyJMLProfile1")) {
            containsDummy1 = true;
         }
         if (profile.getName().equals("DummyJMLProfile2")) {
            containsDummy2 = true;
         }
         if (profile.getName().equals("DummyJMLProfile3")) {
            containsDummy3 = true;
         }
      }

      assertTrue("Dummy Profiles are not included", containsDummy1
            && containsDummy2 && containsDummy3);

   }

}
