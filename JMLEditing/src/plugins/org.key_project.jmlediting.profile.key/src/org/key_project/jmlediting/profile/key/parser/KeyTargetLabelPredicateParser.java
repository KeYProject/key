package org.key_project.jmlediting.profile.key.parser;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;
import static org.key_project.jmlediting.core.parser.util.JavaBasicsParser.ident;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.JMLRefUserParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.PredicateParser;

public class KeYTargetLabelPredicateParser extends
      JMLRefUserParseFunctionKeywordParser {

   @Override
   public String getDescription() {
      return " ('(' <ident>? ')')? <predicate>? ";
   }

   @Override
   protected ParseFunction createParseFunction(
         final IJMLExpressionProfile profile) {
      return seq(opt(brackets(opt(ident()))), opt(new PredicateParser(profile)));
   }

}
