package org.key_project.jmlediting.profile.jmlref.parser;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.ParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;

public class BinarySpecExpressionParser extends ParseFunctionKeywordParser {

   @Override
   protected ParseFunction createParseFunction(final IJMLProfile profile) {
      final ExpressionParser expr = new ExpressionParser(profile);
      return brackets(seq(expr, constant(","), expr));
   }

}
