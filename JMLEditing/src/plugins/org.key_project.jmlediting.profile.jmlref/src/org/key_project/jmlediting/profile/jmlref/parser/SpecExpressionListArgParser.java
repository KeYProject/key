package org.key_project.jmlediting.profile.jmlref.parser;

import static org.key_project.jmlediting.core.parser.ParserBuilder.brackets;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.SpecExpressionParser;

/**
 * A parse for a list of expression arguments.
 * 
 * @author Moritz Lichter
 *
 */
public class SpecExpressionListArgParser extends
      JMLRefUserParseFunctionKeywordParser {

   @Override
   protected ParseFunction createParseFunction(
         final IJMLExpressionProfile profile) {
      final SpecExpressionParser expr = new SpecExpressionParser(profile);
      return brackets(expr.exprList());
   }

   @Override
   public String getDescription() {
      return "'(' <expression> ','? <expression>? ... ')'";
   }

}
