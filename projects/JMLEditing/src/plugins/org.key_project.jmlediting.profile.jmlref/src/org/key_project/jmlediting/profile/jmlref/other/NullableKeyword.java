package org.key_project.jmlediting.profile.jmlref.other;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IToplevelKeyword;

/**
 * Implementation of the nullable keyword for declaration.
 *
 * @author Moritz Lichter
 *
 */
public class NullableKeyword extends AbstractEmptyKeyword implements
      IToplevelKeyword {

   /**
    * Creates a new instance.
    */
   public NullableKeyword() {
      super("nullable");
   }

   @Override
   public String getDescription() {
      return "Any declaration (other than that of a local variable) whose type "
            + "is a reference type is implicitly declared non_null unless "
            + "(explicitly or implicitly) declared nullable. Hence reference "
            + "type declarations are assumed to be non-null by default";
   }

}
