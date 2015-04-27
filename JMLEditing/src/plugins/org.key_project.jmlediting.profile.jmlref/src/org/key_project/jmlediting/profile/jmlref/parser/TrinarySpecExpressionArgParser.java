package org.key_project.jmlediting.profile.jmlref.parser;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;

/**
 * A parser for trinary expression arguments.
 *
 * @author Moritz Lichter
 *
 */
public class TrinarySpecExpressionArgParser extends
      JMLRefUserParseFunctionKeywordParser {

   @Override
   protected ParseFunction createParseFunction(
         final IJMLExpressionProfile profile) {
      final ExpressionParser expr = new ExpressionParser(profile);
      return brackets(seq(expr, constant(","), expr, constant(","), expr));
   }

   @Override
   public String getDescription() {
      return "'(' <expression> ',' <expression> ',' <expression> ')'";
   }

}
