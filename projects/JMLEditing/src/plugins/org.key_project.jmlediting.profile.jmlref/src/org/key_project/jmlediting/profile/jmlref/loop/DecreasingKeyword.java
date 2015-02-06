package org.key_project.jmlediting.profile.jmlref.loop;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IToplevelKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.SemicolonClosedKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.SpecExpressionParser;

/**
 * The implementation of the descreasing keyword for loop invariants.
 *
 * @author Moritz Lichter
 *
 */
public class DecreasingKeyword extends AbstractKeyword implements
      IToplevelKeyword {

   /**
    * Creates a new instance of the descresing keyword.
    */
   public DecreasingKeyword() {
      super("decreasing", "descreases");
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
               final IJMLProfile profile) {
            return new SpecExpressionParser(profile);
         }
      };
   }

}
