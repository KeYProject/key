package org.key_project.jmlediting.profile.jmlref.parser;

import static org.key_project.jmlediting.core.parser.ParserBuilder.brackets;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.SpecExpressionParser;

/**
 * A parser for a type argument.
 * 
 * @author Moritz Lichter
 *
 */
public class TypeArgParser extends JMLRefUserParseFunctionKeywordParser {
   @Override
   protected ParseFunction createParseFunction(
         final IJMLExpressionProfile profile) {
      final SpecExpressionParser parser = new SpecExpressionParser(profile);
      return brackets(parser.typeSpec());
   }

   @Override
   public String getDescription() {
      return "'(' <type> ')'";
   }
}