package org.key_project.jmlediting.core.test.profile;

import static org.junit.Assert.assertTrue;

import java.util.Collections;
import java.util.Set;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.DefaultJMLParser;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.profile.DerivedProfile;
import org.key_project.jmlediting.core.profile.IEditableDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeywordContentDescription;

public class JMLProfileManagementTest {

   private static class DummyProfile implements IJMLProfile {

      private final String name;
      private final String identifier;

      public DummyProfile(final String name, final String identifier) {
         super();
         this.name = name;
         this.identifier = identifier;
      }

      @Override
      public String getName() {
         return this.name;
      }

      @Override
      public String getIdentifier() {
         return this.identifier;
      }

      @Override
      public Set<IKeyword> getSupportedKeywords() {
         return Collections.emptySet();
      }

      @Override
      public Set<IUserDefinedKeywordContentDescription> getSupportedContentDescriptions() {
         return Collections.emptySet();
      }

      @Override
      public IJMLParser createParser() {
         return new DefaultJMLParser(this);
      }

      @Override
      public Set<IKeywordSort> getAvailableKeywordSorts() {
         return Collections.emptySet();
      }

      @Override
      public IEditableDerivedProfile derive(final String id, final String name) {
         return new DerivedProfile<IJMLProfile>(id, name, this) {
         };
      }

   }

   public static class DummyJMLProfile1 extends DummyProfile {

      public DummyJMLProfile1() {
         super("DummyJMLProfile1", DummyJMLProfile1.class.getName());
      }

   }

   public static class DummyJMLProfile2 extends DummyProfile {

      public DummyJMLProfile2() {
         super("DummyJMLProfile2", DummyJMLProfile2.class.getName());
      }

   }

   @Test
   public void testLoadProfiles() {
      final Set<IJMLProfile> availablesProfiles = JMLProfileManagement
            .instance().getAvailableProfiles();
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
