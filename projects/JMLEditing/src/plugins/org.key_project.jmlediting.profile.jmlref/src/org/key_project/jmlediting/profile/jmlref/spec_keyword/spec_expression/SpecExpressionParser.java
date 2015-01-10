package org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;

public class SpecExpressionParser implements ParseFunction {

   private ExpressionParser parser;

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return this.parser.parse(text, start, end);
   }

}
