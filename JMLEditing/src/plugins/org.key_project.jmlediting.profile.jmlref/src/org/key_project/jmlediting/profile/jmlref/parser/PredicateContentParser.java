package org.key_project.jmlediting.profile.jmlref.parser;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.PredicateParser;

/**
 * A parser for a predicate.
 * 
 * @author Moritz Lichter
 *
 */
public class PredicateContentParser extends
      JMLRefUserParseFunctionKeywordParser {

   @Override
   protected ParseFunction createParseFunction(
         final IJMLExpressionProfile profile) {
      return new PredicateParser(profile);
   }

   @Override
   public String getDescription() {
      return "<predicate>";
   }

}
