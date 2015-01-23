package org.key_project.jmlediting.profile.jmlref.primary;

import static org.key_project.jmlediting.core.parser.ParserBuilder.keywords;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.syntax.IJMLPrimary;
import org.key_project.jmlediting.core.profile.syntax.IJMLPrimaryKeyword;

public class KeywordJMLPrimary implements IJMLPrimary {

   private ParseFunction keywordPrimaryParser;

   @Override
   public void setProfile(final IJMLProfile profile) {
      this.keywordPrimaryParser = keywords(
            JMLProfileHelper.filterKeywords(profile, IJMLPrimaryKeyword.class),
            profile);
   }

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return this.keywordPrimaryParser.parse(text, start, end);
   }

}
