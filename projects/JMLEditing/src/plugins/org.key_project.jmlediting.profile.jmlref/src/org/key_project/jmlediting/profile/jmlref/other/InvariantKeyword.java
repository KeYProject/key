package org.key_project.jmlediting.profile.jmlref.other;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IToplevelKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.SemicolonClosedKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.PredicateParser;

/**
 * The implementation of the invariant keyword.
 * 
 * @author Moritz Lichter
 *
 */
public class InvariantKeyword extends AbstractKeyword implements
      IToplevelKeyword {

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
               final IJMLProfile profile) {
            return new PredicateParser(profile);
         }
      };
   }

}
