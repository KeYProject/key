package org.key_project.jmlediting.profile.jmlref.behavior;

import org.key_project.jmlediting.profile.jmlref.KeywordLocale;

public class ExceptionalBehaviorKeyword extends AbstractBehaviorKeyword {

   public ExceptionalBehaviorKeyword(final KeywordLocale lang) {
      super(lang, "exceptional_behavior", "exceptional_behaviour");
   }

   @Override
   public String getDescription() {
      return "An exceptional behavior specification case specifies a precondition which guarantees that the method throws an exception, if it terminates, i.e., a precondition which prohibits the method from terminating normally.";
   }

}
