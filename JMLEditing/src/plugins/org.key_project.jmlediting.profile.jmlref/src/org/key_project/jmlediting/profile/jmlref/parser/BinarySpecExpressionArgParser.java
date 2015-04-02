package org.key_project.jmlediting.profile.jmlref.parser;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;

/**
 * A parser for binary expression arguments in brackets.
 *
 * @author Moritz Lichter
 *
 */
public class BinarySpecExpressionArgParser extends
      JMLRefUserParseFunctionKeywordParser {

   @Override
   protected ParseFunction createParseFunction(
         final IJMLExpressionProfile profile) {
      final ExpressionParser expr = new ExpressionParser(profile);
      return brackets(seq(expr, constant(","), expr));
   }

   @Override
   public String getDescription() {
      return "'(' <expression> ',' <expression> ')'";
   }

}
