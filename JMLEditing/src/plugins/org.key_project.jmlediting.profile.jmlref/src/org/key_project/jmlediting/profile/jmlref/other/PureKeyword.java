package org.key_project.jmlediting.profile.jmlref.other;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyToplevelKeyword;

/**
 * Specifies the pure keyword.
 *
 * @author Moritz Lichter
 *
 */
public class PureKeyword extends AbstractEmptyToplevelKeyword {

   /**
    * Creates a new instance of the pure keyword.
    */
   public PureKeyword() {
      super("pure");
   }

   @Override
   public String getDescription() {
      return "In general terms, a pure feature is one that has no side effects when "
            + "executed. In essence pure only applies to methods and constructors. "
            + "The use of pure for a type declaration is shorthand for applying that "
            + "modifier to all constructors and instance methods in the type.";
   }

}