package org.key_project.jmlediting.profile.jmlref.primary;

import static org.key_project.jmlediting.core.parser.ParserBuilder.keywords;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;

/**
 * The primary which allows all keywords of sort {@link JMLPrimaryKeywordSort}
 * to be parsed as a primary.
 *
 * @author Moritz Lichter
 *
 */
public class KeywordJMLPrimary implements IJMLPrimary {

   /**
    * The parser for all primaries.
    */
   private ParseFunction keywordPrimaryParser;

   @Override
   public void setProfile(final IJMLExpressionProfile profile) {
      this.keywordPrimaryParser = keywords(JMLProfileHelper.filterKeywords(
            profile, JMLPrimaryKeywordSort.INSTANCE), profile);
   }

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return this.keywordPrimaryParser.parse(text, start, end);
   }

}
