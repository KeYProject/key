package org.key_project.jmlediting.core.profile.syntax.user;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.EmptyKeywordParser;

public class EmptyKeywordContent extends
      AbstractUserDefinedKeywordContentDescription {

   @Override
   public String getId() {
      return EmptyKeywordContent.class.getName();
   }

   @Override
   public String getDescription() {
      return " ";
   }

   @Override
   public ClosingCharacterLaw getClosingCharacterLaw() {
      return ClosingCharacterLaw.NOT_ALLOWED;
   }

   @Override
   protected ParseFunction getContentParseFunction(final IJMLProfile profile) {
      return EmptyKeywordParser.getInstance();
   }

}
