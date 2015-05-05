package org.key_project.jmlediting.profile.jmlref.parser;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.SpecExpressionParser;

/**
 * A parser which parses spec expressions.
 *
 * @author Moritz Lichter
 *
 */
public class SpecExpressionContentParser extends
      JMLRefUserParseFunctionKeywordParser {

   @Override
   public String getDescription() {
      return "<expression>";
   }

   @Override
   protected ParseFunction createParseFunction(
         final IJMLExpressionProfile profile) {
      return new SpecExpressionParser(profile);
   }

}
