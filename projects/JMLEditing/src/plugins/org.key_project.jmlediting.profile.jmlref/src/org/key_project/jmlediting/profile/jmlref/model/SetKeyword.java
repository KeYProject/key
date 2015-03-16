package org.key_project.jmlediting.profile.jmlref.model;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.syntax.AbstractToplevelKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.SemicolonClosedKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;

/**
 * The implementation of the set keyword.
 *
 * @author Moritz Lichter
 *
 */
public class SetKeyword extends AbstractToplevelKeyword {

   /**
    * Creates a new instance of the set keyword.
    */
   public SetKeyword() {
      super("set");
   }

   @Override
   public String getDescription() {
      return "A set statement is the equivalent of an assignment statement but "
            + "is within an annotation. It is used to assign a value to a ghost "
            + "variable or to a ghost field.";
   }

   @Override
   public IKeywordParser createParser() {
      return new SemicolonClosedKeywordParser() {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLExpressionProfile profile) {
            /**
             * set-statement ::= set assignment-expr ;
             */
            return new ExpressionParser(profile).assignmentExpr();
         }
      };
   }

}
