package org.key_project.jmlediting.core.profile.syntax.user;

import org.key_project.jmlediting.core.profile.syntax.EmptyKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;

public class EmptyKeywordContent implements
      IUserDefinedKeywordContentDescription {

   @Override
   public String getId() {
      return EmptyKeywordContent.class.getName();
   }

   @Override
   public String getDescription() {
      return " ";
   }

   @Override
   public IKeywordParser createKeywordParser() {
      return EmptyKeywordParser.getInstance();
   }

}
