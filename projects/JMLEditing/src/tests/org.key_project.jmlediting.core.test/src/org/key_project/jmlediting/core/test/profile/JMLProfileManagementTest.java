package org.key_project.jmlediting.core.test.profile;

import static org.junit.Assert.assertTrue;

import java.util.Set;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.DefaultJMLParser;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.profile.AbstractJMLProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;

public class JMLProfileManagementTest {

   public static class DummyJMLProfile1 extends AbstractJMLProfile {

      public DummyJMLProfile1() {
         super("DummyJMLProfile1", DummyJMLProfile1.class.getName());
      }

      @Override
      public IJMLParser createParser() {
         return new DefaultJMLParser(this);
      }

   }

   public static class DummyJMLProfile2 extends AbstractJMLProfile {

      public DummyJMLProfile2() {
         super("DummyJMLProfile2", DummyJMLProfile2.class.getName());
      }

      @Override
      public IJMLParser createParser() {
         return new DefaultJMLParser(this);
      }

   }

   @Test
   public void test() {
      final Set<IJMLProfile> availablesProfiles = JMLProfileManagement
            .getAvailableProfiles();
      assertTrue(
            "Found no available profiles " + availablesProfiles.getClass(),
            !availablesProfiles.isEmpty());

      boolean containsDummy1 = false;
      boolean containsDummy2 = false;
      for (final IJMLProfile profile : availablesProfiles) {
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
