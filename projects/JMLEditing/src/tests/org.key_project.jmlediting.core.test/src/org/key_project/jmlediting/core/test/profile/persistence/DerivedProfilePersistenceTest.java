package org.key_project.jmlediting.core.test.profile.persistence;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.junit.Test;
import org.key_project.jmlediting.core.profile.DerivedProfile;
import org.key_project.jmlediting.core.profile.IDerivedProfile;
import org.key_project.jmlediting.core.profile.IEditableDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.persistence.IDerivedProfilePersistence;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceException;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceFactory;
import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.test.parser.ProfileWrapper;
import org.w3c.dom.Document;

public class DerivedProfilePersistenceTest {

   private final IJMLProfile availableProfile = ProfileWrapper.testProfile;
   private final IDerivedProfilePersistence persistence = ProfilePersistenceFactory
         .createDerivedProfilePersistence();

   @Test
   public void testPersistEmptyDerivedProfile()
         throws ProfilePersistenceException {
      final IDerivedProfile profile = new DerivedProfile("Test",
            "org.test.test", this.availableProfile);
      final Document doc = this.persistence.persist(profile);
      final IDerivedProfile readProfile = this.persistence.read(doc);

      assertEquals("Read name does not match original one", profile.getName(),
            readProfile.getName());
      assertEquals("Read identifier does not match original one",
            profile.getIdentifier(), readProfile.getIdentifier());
      assertEquals("Parent is not equal", profile.getParentProfile(),
            readProfile.getParentProfile());
   }

   @Test
   public void testPersistParentDisablesKeywords()
         throws ProfilePersistenceException {
      final IEditableDerivedProfile profile = new DerivedProfile("Test",
            "org.test.test", this.availableProfile);
      // Pick some parent keywords
      final List<IKeyword> parentKeywords = new ArrayList<IKeyword>(
            this.availableProfile.getSupportedKeywords());
      final Set<IKeyword> disabledKeywords = new HashSet<IKeyword>();

      for (int i = 0; i < parentKeywords.size(); i += 3) {
         final IKeyword disabled = parentKeywords.get(i);
         profile.setParentKeywordDisabled(disabled, true);
         disabledKeywords.add(disabled);
      }
      // require that something was disabled
      if (disabledKeywords.size() == 0) {
         fail("For some reason no keyword was disabled");
      }

      // Persist
      final Document doc = this.persistence.persist(profile);
      final IDerivedProfile readProfile = this.persistence.read(doc);

      // Validate
      for (final IKeyword keyword : this.availableProfile
            .getSupportedKeywords()) {
         if (disabledKeywords.contains(keyword)) {
            assertTrue("Keyword is not disabled in read profile",
                  readProfile.isParentKeywordDisabled(keyword));
         }
         else {
            assertFalse("Keyword is disabled in read profile",
                  readProfile.isParentKeywordDisabled(keyword));
         }
      }
   }

   public static class TestKeyword extends AbstractEmptyKeyword {

      public TestKeyword() {
         super("testkeyword");
      }

      @Override
      public String getDescription() {
         return null;
      }

   }

   @Test
   public void testPersistAdditionalKeywordsFromUserClass()
         throws ProfilePersistenceException {
      final IEditableDerivedProfile profile = new DerivedProfile("Test",
            "org.test.test", this.availableProfile);
      profile.addKeyword(new TestKeyword());

      final Document doc = this.persistence.persist(profile);
      final IDerivedProfile readProfile = this.persistence.read(doc);

      assertEquals("Wrong number of additional keywords", 1, readProfile
            .getAdditionalKeywords().size());
      assertEquals("Class of new keyword is wrong", TestKeyword.class,
            readProfile.getAdditionalKeywords().iterator().next().getClass());
   }

}
