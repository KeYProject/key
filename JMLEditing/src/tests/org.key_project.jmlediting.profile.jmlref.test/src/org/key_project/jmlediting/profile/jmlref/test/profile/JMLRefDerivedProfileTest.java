package org.key_project.jmlediting.profile.jmlref.test.profile;

import static org.key_project.jmlediting.core.test.utilities.ParserTestUtils.testParseComplete;

import java.util.Collections;

import org.junit.Before;
import org.junit.Test;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IEditableDerivedProfile;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.ToplevelKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.user.EmptyKeywordContent;
import org.key_project.jmlediting.core.profile.syntax.user.UserDefinedKeyword;
import org.key_project.jmlediting.profile.jmlref.parser.SpecExpressionContentParser;
import org.key_project.jmlediting.profile.jmlref.quantifier.MinQuantifierKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.EnsuresKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefKeywordSort;
import org.key_project.jmlediting.profile.jmlref.test.utilities.ProfileWrapper;

public class JMLRefDerivedProfileTest {

   private IEditableDerivedProfile derivedProfile;

   @Before
   public void deriveProfile() {
      this.derivedProfile = ProfileWrapper.testProfile.derive(this.getClass()
            .getName(), "DerivedJMLTest");
      // Disable the ensures keyword
      for (final IKeyword enableKeyword : JMLProfileHelper.filterKeywords(
            ProfileWrapper.testProfile, EnsuresKeyword.class)) {
         this.derivedProfile.setParentKeywordDisabled(enableKeyword, true);
      }
      // Disable the min quantifier
      for (final IKeyword minQuantifier : JMLProfileHelper.filterKeywords(
            ProfileWrapper.testProfile, MinQuantifierKeyword.class)) {
         this.derivedProfile.setParentKeywordDisabled(minQuantifier, true);
      }
      // Put two new keywords
      this.derivedProfile.addKeyword(new UserDefinedKeyword(Collections
            .singleton("magic"), ToplevelKeywordSort.INSTANCE,
            new SpecExpressionContentParser(), "A keyword to express magic",
            ';'));
      this.derivedProfile.addKeyword(new UserDefinedKeyword(Collections
            .singleton("\\more_than_everything"), StoreRefKeywordSort.INSTANCE,
            new EmptyKeywordContent(), "Assign to everything", null));
   }

   @Test
   public void testParseMagic() throws ParserException {
      testParseComplete(" magic hello.x() ;",
            this.derivedProfile.createParser());
   }

   @Test
   public void testParseMoreThanEverything() throws ParserException {
      testParseComplete(" assignable \\more_than_everything ;",
            this.derivedProfile.createParser());
   }

   @Test(expected = ParserException.class)
   public void testDontParseEnsures() throws ParserException {
      testParseComplete("\\ensures true;", this.derivedProfile.createParser());
   }

   @Test(expected = ParserException.class)
   public void testDontParseMinQuantifier() throws ParserException {
      testParseComplete("\\requires (\\min int i; x(i));",
            this.derivedProfile.createParser());
   }
}
