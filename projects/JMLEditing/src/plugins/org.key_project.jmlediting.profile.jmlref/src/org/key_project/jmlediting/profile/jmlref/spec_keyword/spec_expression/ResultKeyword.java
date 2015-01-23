package org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IJMLPrimaryKeyword;

/**
 * Implementation of the result keyword.
 *
 * @author Moritz Lichter
 *
 */
public class ResultKeyword extends AbstractEmptyKeyword implements
      IJMLPrimaryKeyword {

   /**
    * Creates a new instance for the result keyword.
    */
   public ResultKeyword() {
      super("\\result");
   }

   @Override
   public String getDescription() {
      return "The primary \result can only be used in ensures, duration, "
            + "and workingspace clauses of a non-void method. Its value "
            + "is the value returned by the method.";
   }

}
