package org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;

public class PredicateParser extends ExpressionParser {

   private SpecExpressionParser expressionParser;

   public PredicateParser(final IJMLProfile profile) {
      super(profile);
      // TODO Auto-generated constructor stub
   }

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return this.expressionParser.parse(text, start, end);
   }

}
