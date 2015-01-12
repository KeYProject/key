package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserBuilder;
import org.key_project.jmlediting.core.profile.IJMLProfile;

public abstract class ParseFunctionGenericKeywordParser extends
      ParseFunctionKeywordParser {

   private final int type;

   public ParseFunctionGenericKeywordParser(final int type) {
      super();
      this.type = type;
   }

   protected abstract ParseFunction createContentParseFunction(
         final IJMLProfile profile);

   @Override
   protected ParseFunction createParseFunction(final IJMLProfile profile) {
      return ParserBuilder.closedBy(this.type,
            this.createContentParseFunction(profile), ';');
   }

}
