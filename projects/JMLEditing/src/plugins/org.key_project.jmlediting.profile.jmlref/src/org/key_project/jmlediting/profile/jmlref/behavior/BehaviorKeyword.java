package org.key_project.jmlediting.profile.jmlref.behavior;

import org.key_project.jmlediting.profile.jmlref.KeywordLocale;

/**
 * Class for the default behavior keyword.
 *
 * @author Moritz Lichter
 *
 */
public class BehaviorKeyword extends AbstractBehaviorKeyword {

   /**
    * Creates a new instance for the behavior keyword.
    *
    * @param lang
    *           the locale for AE/BE
    */
   public BehaviorKeyword(final KeywordLocale lang) {
      super(lang, "behavior", "behaviour");
   }

   @Override
   public String getDescription() {
      return "The behavior specification case is the most general form of "
            + "specification case. All other forms of specification cases "
            + "simply provide some syntactic sugar for special kinds of behavior "
            + "specification cases.";
   }

}
