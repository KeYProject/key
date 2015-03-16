package org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression;

import org.key_project.jmlediting.core.profile.syntax.EmptyKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.primary.AbstractJMLPrimaryKeyword;

/**
 * Implementation of the result keyword.
 *
 * @author Moritz Lichter
 *
 */
public class ResultKeyword extends AbstractJMLPrimaryKeyword {

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

   @Override
   public IKeywordParser createParser() {
      return EmptyKeywordParser.getInstance();
   }

}
