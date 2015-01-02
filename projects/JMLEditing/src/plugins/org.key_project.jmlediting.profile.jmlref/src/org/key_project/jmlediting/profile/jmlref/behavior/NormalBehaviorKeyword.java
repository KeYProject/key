package org.key_project.jmlediting.profile.jmlref.behavior;

import org.key_project.jmlediting.profile.jmlref.KeywordLocale;

/**
 * The normal_behavior keyword.
 *
 * @author Moritz Lichter
 *
 */
public class NormalBehaviorKeyword extends AbstractBehaviorKeyword {

   /**
    * Creates a new instance for the normal_behavior keyword.
    *
    * @param lang
    *           the locale for AE/BE
    */
   public NormalBehaviorKeyword(final KeywordLocale lang) {
      super(lang, "normal_behavior", "normal_behaviour");
   }

   @Override
   public String getDescription() {
      return "A normal_behavior specification case is just syntactic sugar "
            + "for a behavior specification case with an implicit signals "
            + "clause \"signals (java.lang.Exception) false;\" ruling out abrupt "
            + "termination, i.e., the throwing of any exception.";
   }

}
