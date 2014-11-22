package org.key_project.jmlediting.core.test.profile;

import static org.junit.Assert.assertTrue;

import java.util.Collections;
import java.util.Set;

import org.junit.Test;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.AbstractJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorKeyword;
import org.key_project.jmlediting.core.profile.syntax.ISpecificationStatementKeyword;

public class JMLProfileManagementTest {

   public static class DummyJMLProfile1 extends AbstractJMLProfile {

      public DummyJMLProfile1() {
         super( "DummyJMLProfile1",DummyJMLProfile1.class.getName());
      }

   }

   public static class DummyJMLProfile2 extends AbstractJMLProfile {

      public DummyJMLProfile2() {
         super( "DummyJMLProfile2",DummyJMLProfile2.class.getName());
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
