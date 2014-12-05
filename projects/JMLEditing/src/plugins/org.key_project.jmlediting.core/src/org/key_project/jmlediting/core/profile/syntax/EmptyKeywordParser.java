package org.key_project.jmlediting.core.profile.syntax;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParserException;

public final class EmptyKeywordParser implements IKeywordParser {

   private static final EmptyKeywordParser INSTANCE = new EmptyKeywordParser();

   public static EmptyKeywordParser getInstance() {
      return INSTANCE;
   }

   private EmptyKeywordParser() {
   }

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return null;
   }

}
