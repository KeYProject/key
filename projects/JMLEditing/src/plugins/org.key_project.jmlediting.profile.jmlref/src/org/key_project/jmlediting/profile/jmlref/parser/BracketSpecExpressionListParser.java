package org.key_project.jmlediting.profile.jmlref.parser;

import static org.key_project.jmlediting.core.parser.ParserBuilder.brackets;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.ParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.SpecExpressionParser;

public class BracketSpecExpressionListParser extends ParseFunctionKeywordParser {

   @Override
   protected ParseFunction createParseFunction(final IJMLProfile profile) {
      final SpecExpressionParser expr = new SpecExpressionParser(profile);
      return brackets(expr.exprList());
   }

}
