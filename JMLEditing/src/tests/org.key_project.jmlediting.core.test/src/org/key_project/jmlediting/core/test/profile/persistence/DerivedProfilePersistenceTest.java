package org.key_project.jmlediting.core.test.profile.persistence;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.junit.Test;
import org.key_project.jmlediting.core.profile.IDerivedProfile;
import org.key_project.jmlediting.core.profile.IEditableDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.core.profile.persistence.IDerivedProfilePersistence;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceException;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceFactory;
import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.ToplevelKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeyword;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeywordContentDescription;
import org.key_project.jmlediting.core.profile.syntax.user.UserDefinedKeyword;
import org.key_project.jmlediting.core.test.utilities.profile.PersistenceParentProfile;

public class DerivedProfilePersistenceTest {

   private final IJMLProfile availableProfile = JMLProfileManagement.instance()
         .getProfileFromIdentifier(PersistenceParentProfile.class.getName());
   private final IDerivedProfilePersistence persistence = ProfilePersistenceFactory
         .createDerivedProfilePersistence();

   @Test
   public void testPersistEmptyDerivedProfile()
         throws ProfilePersistenceException {
      final IDerivedProfile profile = this.availableProfile.derive(
            "org.test.test", "Test");
      final String doc = this.persistence.persist(profile);
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
      final IEditableDerivedProfile profile = this.availableProfile.derive(
            "org.test.test", "Test");
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
      final String doc = this.persistence.persist(profile);
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

      @Override
      public IKeywordSort getSort() {
         return ToplevelKeywordSort.INSTANCE;
      }
   }

   // Illegal for persistence because the keyword has a non nullary constructor
   public static class IllegalTestKeyword extends AbstractEmptyKeyword {

      public IllegalTestKeyword(final String keyword) {
         super(keyword);
      }

      @Override
      public String getDescription() {
         return null;
      }

      @Override
      public IKeywordSort getSort() {
         return null;
      }

   }

   @Test
   public void testPersistAdditionalKeywordsFromUserClass()
         throws ProfilePersistenceException {
      final IEditableDerivedProfile profile = this.availableProfile.derive(
            "org.test.test", "Test");
      profile.addKeyword(new TestKeyword());

      final String doc = this.persistence.persist(profile);
      final IDerivedProfile readProfile = this.persistence.read(doc);

      assertEquals("Wrong number of additional keywords", 1, readProfile
            .getAdditionalKeywords().size());
      assertEquals("Class of new keyword is wrong", TestKeyword.class,
            readProfile.getAdditionalKeywords().iterator().next().getClass());
   }

   @Test(expected = ProfilePersistenceException.class)
   public void testPersitKeywordWithNonNullaryConstructor()
         throws ProfilePersistenceException {
      final IEditableDerivedProfile profile = this.availableProfile.derive(
            "org.test.illegal", "IllegalTest");
      profile.addKeyword(new IllegalTestKeyword("illegal_keyword"));

      // Should throw an exception
      this.persistence.persist(profile);
   }

   @Test
   public void testPersistUserDefinedKeyword()
         throws ProfilePersistenceException {
      final IUserDefinedKeywordContentDescription contentDescription = this.availableProfile
            .getSupportedContentDescriptions().iterator().next();
      final Character closingChar = ';';
      final String keyword = "mykeyword";
      final String keywrodDescription = "My own keyword.";
      this.testPersistUserDefinedKeyword(new UserDefinedKeyword(Collections
            .singleton(keyword), ToplevelKeywordSort.INSTANCE,
            contentDescription, keywrodDescription, closingChar));

   }

   @Test
   public void testPersistUserDefinedKeywordEmptyDescription()
         throws ProfilePersistenceException {
      final IUserDefinedKeywordContentDescription contentDescription = this.availableProfile
            .getSupportedContentDescriptions().iterator().next();
      final Character closingChar = ';';
      final String keyword = "mykeyword";
      final String keywrodDescription = "";
      this.testPersistUserDefinedKeyword(new UserDefinedKeyword(Collections
            .singleton(keyword), ToplevelKeywordSort.INSTANCE,
            contentDescription, keywrodDescription, closingChar));
   }

   private void testPersistUserDefinedKeyword(final IUserDefinedKeyword keyword)
         throws ProfilePersistenceException {
      final IEditableDerivedProfile profile = this.availableProfile.derive(
            "org.test.userdef", "IllegalTest");

      profile.addKeyword(keyword);

      final String doc = this.persistence.persist(profile);
      final IDerivedProfile readProfile = this.persistence.read(doc);

      assertEquals("User defined keyword not loaded", 1, readProfile
            .getAdditionalKeywords().size());
      final IKeyword newKeyword = readProfile.getAdditionalKeywords()
            .iterator().next();
      assertTrue("Keyword loaded does not implement IUserDefinedKeyword",
            newKeyword instanceof IUserDefinedKeyword);
      final IUserDefinedKeyword newUserKeyword = (IUserDefinedKeyword) newKeyword;
      assertEquals("Wrong number of keywords", 1, newKeyword.getKeywords()
            .size());
      assertEquals("Wrong keyword", keyword.getKeywords(),
            newKeyword.getKeywords());
      assertEquals("Wrong description", keyword.getDescription(),
            newKeyword.getDescription());
      assertEquals("Wrong content description",
            keyword.getContentDescription(),
            newUserKeyword.getContentDescription());
      assertEquals("Wrong closing character", keyword.getClosingCharacter(),
            newUserKeyword.getClosingCharacter());
      assertEquals("Wrong sort", ToplevelKeywordSort.INSTANCE,
            newUserKeyword.getSort());

   }

}
