package org.key_project.jmlediting.profile.jmlref.behavior;

import org.key_project.jmlediting.profile.jmlref.KeywordLocale;

/**
 * The exceptional_behavior keyword.
 *
 * @author Moritz Lichter
 *
 */
public class ExceptionalBehaviorKeyword extends AbstractBehaviorKeyword {

   /**
    * Creates a new instance for the exceptional_behavior keyword.
    *
    * @param lang
    *           the locale for AE/BE
    */
   public ExceptionalBehaviorKeyword(final KeywordLocale lang) {
      super(lang, "exceptional_behavior", "exceptional_behaviour");
   }

   @Override
   public String getDescription() {
      return "An exceptional behavior specification case specifies a precondition "
            + "which guarantees that the method throws an exception, if it "
            + "terminates, i.e., a precondition which prohibits the method from "
            + "terminating normally.";
   }

}
