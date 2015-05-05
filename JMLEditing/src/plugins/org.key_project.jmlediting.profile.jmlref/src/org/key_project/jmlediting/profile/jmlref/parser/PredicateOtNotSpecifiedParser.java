package org.key_project.jmlediting.profile.jmlref.parser;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.PredicateOrNotParser;

/**
 * A parser for predicates allowing not-specified.
 *
 * @author Moritz Lichter
 *
 */
public class PredicateOtNotSpecifiedParser extends
      JMLRefUserParseFunctionKeywordParser {
   @Override
   protected ParseFunction createParseFunction(
         final IJMLExpressionProfile profile) {
      return new PredicateOrNotParser(profile);
   }

   @Override
   public String getDescription() {
      return "<predicate> | '\\not_specified'";
   }
}