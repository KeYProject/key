package org.key_project.jmlediting.core.parser.internal;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.IRecursiveParseFunction;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;

public class RecursiveParseFunction implements IRecursiveParseFunction {

   private ParseFunction function = null;

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return this.function.parse(text, start, end);
   }

   @Override
   public void defineAs(final ParseFunction p) {
      this.function = p;
   }

}
