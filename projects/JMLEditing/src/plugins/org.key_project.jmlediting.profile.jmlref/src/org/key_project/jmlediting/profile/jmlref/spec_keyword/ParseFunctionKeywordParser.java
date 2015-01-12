package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;

public abstract class ParseFunctionKeywordParser implements IKeywordParser {

   private ParseFunction mainParser;

   protected abstract ParseFunction createParseFunction(IJMLProfile profile);

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return this.mainParser.parse(text, start, end);
   }

   @Override
   public void setProfile(final IJMLProfile profile) {
      this.mainParser = this.createParseFunction(profile);
   }

}
