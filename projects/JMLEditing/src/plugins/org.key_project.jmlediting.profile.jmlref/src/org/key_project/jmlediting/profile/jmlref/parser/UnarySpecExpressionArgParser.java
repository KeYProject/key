package org.key_project.jmlediting.profile.jmlref.parser;

import static org.key_project.jmlediting.core.parser.ParserBuilder.brackets;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.SpecExpressionParser;

/**
 * Parser to parse a unary expression arguments in brackets.
 *
 * @author Moritz Lichter
 *
 */
public class UnarySpecExpressionArgParser extends
      JMLRefUserParseFunctionKeywordParser {

   @Override
   protected ParseFunction createParseFunction(
         final IJMLExpressionProfile profile) {
      final SpecExpressionParser expr = new SpecExpressionParser(profile);
      return brackets(expr);
   }

   @Override
   public String getDescription() {
      return "'(' <expression> ')'";
   }

}
