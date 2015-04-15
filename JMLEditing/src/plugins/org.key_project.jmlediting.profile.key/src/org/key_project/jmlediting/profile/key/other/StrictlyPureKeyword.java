package org.key_project.jmlediting.profile.key.other;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyToplevelKeyword;

/**
 * Strictly pure keyword which is more strict than the JML pure keyword.
 *
 * @author Moritz Lichter
 *
 */
public class StrictlyPureKeyword extends AbstractEmptyToplevelKeyword {

   /**
    * Creates a new instance.
    */
   public StrictlyPureKeyword() {
      super("strictly_pure");
   }

   @Override
   public String getDescription() {
      return "In general terms, a pure feature is one that has no side "
            + "effects when executed. In essence pure only applies to methods "
            + "and constructors. The use of pure for a type declaration is "
            + "shorthand for applying that modifier to all constructors and "
            + "instance methods in the type. <br> <b>The strictly_pure keyword "
            + "also disallows to create new objects.</b>";
   }

}
