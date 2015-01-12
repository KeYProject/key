package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserBuilder;
import org.key_project.jmlediting.core.profile.IJMLProfile;

public abstract class ParseFunctionGenericKeywordParser extends
      ParseFunctionKeywordParser {

   protected abstract ParseFunction createContentParseFunction(
         final IJMLProfile profile);

   @Override
   protected ParseFunction createParseFunction(final IJMLProfile profile) {
      return ParserBuilder.closedBy(NodeTypes.KEYWORD_CONTENT,
            this.createContentParseFunction(profile), ';');
   }

}
