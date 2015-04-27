package org.key_project.jmlediting.profile.jmlref.other;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyToplevelKeyword;

/**
 * Specifies the helper keyword.
 *
 * @author Moritz Lichter
 *
 */
public class HelperKeyword extends AbstractEmptyToplevelKeyword {

   /**
    * Creates a new instance for the helper keyword.
    */
   public HelperKeyword() {
      super("helper");
   }

   @Override
   public String getDescription() {
      return "The helper modifier may be used on a method that is either "
            + "pure or private or on a private constructor to say that its "
            + "specification is not augmented by invariants and history "
            + "constraints that would otherwise be relevant.";
   }

}
