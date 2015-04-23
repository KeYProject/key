package org.key_project.jmlediting.profile.jmlref.loop;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.syntax.AbstractToplevelKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordValidator;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.SemicolonClosedKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.SpecExpressionParser;
import org.key_project.jmlediting.profile.jmlref.validator.LoopInvariantValidator;

/**
 * The implementation of the decreasing keyword for loop invariants.
 *
 * @author Moritz Lichter
 *
 */
public class DecreasingKeyword extends AbstractToplevelKeyword {

   /**
    * Creates a new instance of the decreasing keyword.
    */
   public DecreasingKeyword() {
      super("decreasing", "decreases");
   }

   @Override
   public String getDescription() {
      return "A variant-function is used to help prove termination of a loop statement. "
            + "It specifies an expression of type long or int that must be no less than 0 "
            + "when the loop is executing, and must decrease by at least one (1) each "
            + "time around the loop.";
   }

   @Override
   public IKeywordParser createParser() {
      return new SemicolonClosedKeywordParser() {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLExpressionProfile profile) {
            return new SpecExpressionParser(profile);
         }
      };
   }

   @Override
   public IKeywordValidator getKeywordValidator() {
      return new LoopInvariantValidator();
   }

}
