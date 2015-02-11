package org.key_project.jmlediting.core.test.profile;

import static org.junit.Assert.*;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.junit.Test;
import org.key_project.jmlediting.core.parser.DefaultJMLParser;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.profile.AbstractJMLProfile;
import org.key_project.jmlediting.core.profile.DerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

public class BasicDerivedProfileTest {

   private static final class SimpleKeyword extends AbstractEmptyKeyword {

      public SimpleKeyword(final String keyword) {
         super(keyword);
      }

      @Override
      public String getDescription() {
         return null;
      }

      @Override
      public String toString() {
         return this.getKeywords().iterator().next();
      }

   }

   private static final IKeyword baseKeyword1 = new SimpleKeyword("Base1");
   private static final IKeyword baseKeyword2 = new SimpleKeyword("Base2");
   private static final IKeyword baseKeyword3 = new SimpleKeyword("Base3");
   private static final IKeyword derivedKeyword1 = new SimpleKeyword("Derived1");
   private static final IKeyword derivedKeyword2 = new SimpleKeyword("Derived2");

   private static final Object key = new Object();
   private static final Object baseValue = new Object();
   private static final Object derivedValue = new Object();

   private static final class BaseProfile extends AbstractJMLProfile {

      public BaseProfile() {
         this.getSupportedKeywordsInternal().addAll(
               Arrays.asList(baseKeyword1, baseKeyword2, baseKeyword3));
      }

      @Override
      public String getName() {
         return "BaseProfile";
      }

      @Override
      public String getIdentifier() {
         return this.getClass().getName();
      }

      @Override
      public IJMLParser createParser() {
         return new DefaultJMLParser(this);
      }

      public void putExtension() {
         this.putExtension(key, baseValue, Object.class);
      }

   }

   private static final class TestDerivedProfile extends DerivedProfile {

      public TestDerivedProfile(final String name, final String identifier,
            final IJMLProfile parentProfile) {
         super(name, identifier, parentProfile);
      }

      public void putExtension() {
         this.putExtension(key, derivedValue, Object.class);
      }

   }

   private final BaseProfile parentProfile = new BaseProfile();
   private final TestDerivedProfile derivedProfile = new TestDerivedProfile(
         "Derived", this.getClass().getName(), this.parentProfile);

   @Test
   public void testCorrectParentProfile() {
      assertTrue("Derived profile has wrong parent profile",
            this.derivedProfile.getParentProfile() == this.parentProfile);
   }

   @Test
   public void testParserNotNull() {
      assertNotNull("Parser is null",
            this.derivedProfile.createParser() != null);
   }

   @Test
   public void testSetName() {
      assertEquals("Wrong initial name", "Derived",
            this.derivedProfile.getName());
      this.derivedProfile.setName("DerivedNew");
      assertEquals("Wrong set name", "DerivedNew",
            this.derivedProfile.getName());
   }

   @Test
   public void testCorrectIdentifier() {
      assertEquals("Profile has wrong identifier", this.getClass().getName(),
            this.derivedProfile.getIdentifier());
   }

   @Test
   public void testUnconfiguredDerivedProfileSupportesParentKeywords() {
      assertEquals(
            "Unconfigured Derived profile does support the same keywords as parent",
            this.parentProfile.getSupportedKeywords(),
            this.derivedProfile.getSupportedKeywords());
   }

   @Test
   public void testDerivedProfilesSupportsParentPrimaries() {
      assertEquals("Derived profile does not support primaries of parent",
            this.parentProfile.getSupportedPrimaries(),
            this.derivedProfile.getSupportedPrimaries());
   }

   @Test
   public void testAddNewKeywordsToDerived() {
      this.derivedProfile.addKeyword(derivedKeyword1);
      assertEquals("Additional keywords does not contains first",
            set(derivedKeyword1), this.derivedProfile.getAdditionalKeywords());
      assertEquals("Derived profile does not support first added keyword",
            set(this.parentProfile, derivedKeyword1),
            this.derivedProfile.getSupportedKeywords());

      this.derivedProfile.addKeyword(derivedKeyword2);
      this.derivedProfile.addKeyword(derivedKeyword2);
      this.derivedProfile.addKeyword(derivedKeyword2);

      assertEquals("Additional keywords does not contains second",
            set(derivedKeyword1, derivedKeyword2),
            this.derivedProfile.getAdditionalKeywords());
      assertEquals("Derived profile does not support second added keyword",
            set(this.parentProfile, derivedKeyword1, derivedKeyword2),
            this.derivedProfile.getSupportedKeywords());
   }

   @Test
   public void testRemoveKeywordsFromDerived() {
      this.derivedProfile.addKeyword(derivedKeyword1);
      this.derivedProfile.removeKeyword(derivedKeyword1);
      this.derivedProfile.removeKeyword(derivedKeyword1);
      assertEquals("Keyword not correctly removed from derived profile",
            this.parentProfile.getSupportedKeywords(),
            this.derivedProfile.getSupportedKeywords());
   }

   @Test
   public void testEnabledKeywordMarkedAsEnabled() {
      assertFalse("Enabled keyword is not marked as enabled",
            this.derivedProfile.isParentKeywordDisabled(baseKeyword1));
   }

   @Test
   public void testDisableParentKeyword() {
      this.derivedProfile.setParentKeywordDisabled(baseKeyword1, true);
      assertTrue("Keyword is not marked as disabled",
            this.derivedProfile.isParentKeywordDisabled(baseKeyword1));
      assertEquals("Keyword is not disabled", set(baseKeyword2, baseKeyword3),
            this.derivedProfile.getSupportedKeywords());
   }

   @Test
   public void testEnableParentKeyword() {
      this.derivedProfile.setParentKeywordDisabled(baseKeyword2, true);
      this.derivedProfile.setParentKeywordDisabled(baseKeyword3, true);
      this.derivedProfile.setParentKeywordDisabled(baseKeyword3, false);
      this.derivedProfile.setParentKeywordDisabled(baseKeyword1, false);
      assertEquals("Keywords not enabled correctly",
            set(baseKeyword1, baseKeyword3),
            this.derivedProfile.getSupportedKeywords());
   }

   @Test
   public void testGetSupportedKeywordsSame() {
      this.derivedProfile.addKeyword(derivedKeyword1);
      this.derivedProfile.addKeyword(derivedKeyword2);
      this.derivedProfile.setParentKeywordDisabled(baseKeyword2, true);
      final Set<IKeyword> supported1 = this.derivedProfile
            .getSupportedKeywords();
      this.derivedProfile.addKeyword(derivedKeyword1);
      final Set<IKeyword> supported2 = this.derivedProfile
            .getSupportedKeywords();
      this.derivedProfile.setParentKeywordDisabled(baseKeyword2, true);
      final Set<IKeyword> supported3 = this.derivedProfile
            .getSupportedKeywords();

      final Set<IKeyword> expected = set(baseKeyword1, baseKeyword3,
            derivedKeyword1, derivedKeyword2);
      assertEquals("First supported keywords wrong", expected, supported1);
      assertEquals("Second supported keywords wrong", expected, supported2);
      assertEquals("Third supported keywords wrong", expected, supported3);
   }

   @Test
   public void testExtensions() {
      assertEquals("Test no extensions", Collections.emptySet(),
            this.derivedProfile.getExtensions(key, Object.class));
   }

   @Test
   public void testOnlyParentExtensions() {
      this.parentProfile.putExtension();
      assertEquals("No extension of parent", set(baseValue),
            this.derivedProfile.getExtensions(key, Object.class));
   }

   @Test
   public void testOnlyDerivedExtensions() {
      this.derivedProfile.putExtension();
      assertEquals("No extension of derived", set(derivedValue),
            this.derivedProfile.getExtensions(key, Object.class));
   }

   @Test
   public void testBothExtensions() {
      this.parentProfile.putExtension();
      this.derivedProfile.putExtension();
      assertEquals("Wrong extension of both", set(derivedValue, baseValue),
            this.derivedProfile.getExtensions(key, Object.class));
   }

   @Test(expected = IllegalArgumentException.class)
   public void testAddNullKeyword() {
      this.derivedProfile.addKeyword(null);
   }

   @Test(expected = IllegalArgumentException.class)
   public void testRemoveNullKeyword() {
      this.derivedProfile.removeKeyword(null);
   }

   @Test(expected = IllegalArgumentException.class)
   public void testEnableNullKeyword() {
      this.derivedProfile.setParentKeywordDisabled(null, false);
   }

   @Test(expected = IllegalArgumentException.class)
   public void testEnableKeywordNotOfParentProfile() {
      this.derivedProfile.setParentKeywordDisabled(derivedKeyword1, false);
   }

   @Test(expected = IllegalArgumentException.class)
   public void testIsDisabledNoParentProfile() {
      this.derivedProfile.isParentKeywordDisabled(derivedKeyword1);
   }

   @Test(expected = IllegalArgumentException.class)
   public void testSetNullName() {
      this.derivedProfile.setName(null);
   }

   @Test(expected = IllegalArgumentException.class)
   public void testInitializeWithoutParent() {
      new DerivedProfile("a", "b", null);
   }

   @Test(expected = IllegalArgumentException.class)
   public void testInitializeWithoutName() {
      new DerivedProfile(null, "a", this.parentProfile);
   }

   @Test(expected = IllegalArgumentException.class)
   public void testInitializeWithoutIdentifier() {
      new DerivedProfile("a", null, this.parentProfile);
   }

   private static <T> Set<T> set(final T... keywords) {
      return new HashSet<T>(Arrays.asList(keywords));
   }

   private static Set<IKeyword> set(final IJMLProfile profile,
         final IKeyword... iKeywords) {
      final HashSet<IKeyword> newSet = new HashSet<IKeyword>(
            profile.getSupportedKeywords());
      newSet.addAll(Arrays.asList(iKeywords));
      return newSet;
   }

}
