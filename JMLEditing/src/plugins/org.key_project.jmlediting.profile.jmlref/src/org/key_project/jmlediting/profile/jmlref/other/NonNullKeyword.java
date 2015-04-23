package org.key_project.jmlediting.profile.jmlref.other;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyToplevelKeyword;

/**
 * Non null keyword for declarations.
 *
 * @author Moritz Lichter
 *
 */
public class NonNullKeyword extends AbstractEmptyToplevelKeyword {

   /**
    * Creates a new instance.
    */
   public NonNullKeyword() {
      super("non_null");
   }

   @Override
   public String getDescription() {
      return "Any declaration (other than that of a local variable) whose type "
            + "is a reference type is implicitly declared non_null unless "
            + "(explicitly or implicitly) declared nullable. Hence reference "
            + "type declarations are assumed to be non-null by default";
   }

}
