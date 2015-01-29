package org.key_project.jmlediting.profile.jmlref.loop;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IToplevelKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.ParseFunctionGenericKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.PredicateParser;

/**
 * The implementation of the loop invariant keyword.
 * 
 * @author Moritz Lichter
 *
 */
public class LoopInvariantKeyword extends AbstractKeyword implements
      IToplevelKeyword {

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
      return new ParseFunctionGenericKeywordParser() {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLProfile profile) {
            return new PredicateParser(profile);
         }
      };
   }

}
