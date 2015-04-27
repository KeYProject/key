package org.key_project.jmlediting.profile.jmlref.other;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyToplevelKeyword;

/**
 * Specifies the also keyword.
 *
 * @author Moritz Lichter
 *
 */
public class AlsoKeyword extends AbstractEmptyToplevelKeyword {

   /**
    * Creates a new instance for the also keyword.
    */
   public AlsoKeyword() {
      super("also");
   }

   @Override
   public String getDescription() {
      return "A method-specification can include any number of spec-cases, joined "
            + "by the keyword also, as well as a redundant-spec.\nA method-specification "
            + "of a method in a class or interface must start with the keyword "
            + "also if (and only if) this method is already declared in the parent "
            + "type that the current type extends, in one of the interfaces the "
            + "class implements, or in a previous file of the refinement sequence for this type.";
   }

}
