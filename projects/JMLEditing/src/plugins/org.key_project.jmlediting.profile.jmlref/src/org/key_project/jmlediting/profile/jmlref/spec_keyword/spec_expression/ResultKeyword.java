package org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;

public class ResultKeyword extends AbstractEmptyKeyword implements
      IJMLPrimaryKeyword {

   public ResultKeyword() {
      super("\\result");
      // TODO Auto-generated constructor stub
   }

   @Override
   public String getDescription() {
      return "The primary \result can only be used in ensures, duration, "
            + "and workingspace clauses of a non-void method. Its value "
            + "is the value returned by the method.";
   }

}
