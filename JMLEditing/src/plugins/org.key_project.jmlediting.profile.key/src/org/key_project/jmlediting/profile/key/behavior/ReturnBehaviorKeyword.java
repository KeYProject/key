package org.key_project.jmlediting.profile.key.behavior;

import org.key_project.jmlediting.core.profile.syntax.AbstractToplevelKeyword;
import org.key_project.jmlediting.core.profile.syntax.EmptyKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;

public class ReturnBehaviorKeyword extends AbstractToplevelKeyword {

   public ReturnBehaviorKeyword() {
      super("return_behavior");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywordParser createParser() {
      return EmptyKeywordParser.getInstance();
   }

}
