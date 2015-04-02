package org.key_project.jmlediting.profile.jmlref.other;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.syntax.AbstractToplevelKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.SemicolonClosedKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.PredicateParser;

/**
 * The implementation of the invariant keyword.
 *
 * @author Moritz Lichter
 *
 */
public class InvariantKeyword extends AbstractToplevelKeyword {

   /**
    * Creates a new instance of the invariant keyword.
    */
   public InvariantKeyword() {
      super("invariant");
   }

   @Override
   public String getDescription() {
      return "Invariants are properties that have to hold in all visible states.";
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

}
