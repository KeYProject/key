package org.key_project.jmlediting.core.test;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.Set;

import org.eclipse.core.runtime.CoreException;
import org.junit.Test;
import org.key_project.jmlediting.core.IJMLProfile;
import org.key_project.jmlediting.core.JMLProfileManagement;

public class JMLProfileManagementTest {
   
   public static class DummyJMLProfile1 implements IJMLProfile {

      @Override
      public String getName() {
         return "DummyJMLProfile1";
      }
      
   }

   @Test
   public void test() {
      try {
         Set<IJMLProfile> availablesProfiles = JMLProfileManagement.getAvailableProfiles();
         assertTrue("Found no available profiles " + availablesProfiles.getClass(), !availablesProfiles.isEmpty());
         
         boolean containsDummy = false;
         for (IJMLProfile profile : availablesProfiles) {
            if (profile.getName().equals("DummyJMLProfile1")) {
               containsDummy = true;
            }
         }
         
         assertTrue("Dummy Profile is not included", containsDummy);
      }
      catch (CoreException e) {
         fail("Get available profiles throwed exception! " + e.getMessage());
      }
   }

}
