package org.key_project.jmlediting.core.profile.syntax.user;

import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserBuilder;
import org.key_project.jmlediting.core.profile.IJMLProfile;

public abstract class AbstractUserDefinedKeywordContentDescription implements
      IUserDefinedKeywordContentDescription {

   protected abstract ParseFunction getContentParseFunction(IJMLProfile profile);

   @Override
   public ParseFunction getContentParseFunction(final IJMLProfile profile,
         final Character closingChar) {
      final ParseFunction content = this.getContentParseFunction(profile);
      if (closingChar == null) {
         return content;
      }
      else {
         return ParserBuilder.closedBy(NodeTypes.NODE, content, closingChar);
      }
   }
}
