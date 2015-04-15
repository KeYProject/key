package org.key_project.jmlediting.profile.jmlref.loop;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.syntax.AbstractToplevelKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordValidator;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.SemicolonClosedKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.PredicateParser;
import org.key_project.jmlediting.profile.jmlref.validator.LoopInvariantValidator;

/**
 * The implementation of the loop invariant keyword.
 *
 * @author Moritz Lichter
 *
 */
public class LoopInvariantKeyword extends AbstractToplevelKeyword {

   /**
    * Creates a new instance of the loop invariant keyword.
    */
   public LoopInvariantKeyword() {
      super("loop_invariant", "maintaining");

   }

   @Override
   public String getDescription() {
      return "A loop-invariant is used to help prove partial correctness of a loop statement."
            + " The loop invariant holds at the beginning of each iteration of the loop.";
   }

   @Override
   public IKeywordParser createParser() {
      return new SemicolonClosedKeywordParser() {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLExpressionProfile profile) {
            return new PredicateParser(profile);
         }
      };
   }

   @Override
   public IKeywordValidator getKeywordValidator() {
      return new LoopInvariantValidator();
   }

}
