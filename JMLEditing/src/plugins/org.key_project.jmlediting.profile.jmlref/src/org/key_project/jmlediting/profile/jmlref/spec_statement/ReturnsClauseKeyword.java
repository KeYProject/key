package org.key_project.jmlediting.profile.jmlref.spec_statement;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserBuilder;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.SemicolonClosedKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AbstractGenericSpecificationKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.PredicateOrNotParser;

/**
 * Implementation of the returns clause keyword.
 *
 * @author Moritz Lichter
 *
 */
public class ReturnsClauseKeyword extends AbstractGenericSpecificationKeyword {

   /**
    * Returns a new instance of the returns clause keyword.
    */
   public ReturnsClauseKeyword() {
      super("returns", "returns_redundantly");
   }

   @Override
   public String getDescription() {
      return "The meaning of the returns-clause is that if the statement "
            + "that implements the specification statement executes a "
            + "return, then the given predicate (if any) must hold in "
            + "the state following evaluation of the return value, but "
            + "just before the return is executed.";
   }

   @Override
   public IKeywordParser createParser() {
      return new SemicolonClosedKeywordParser() {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLExpressionProfile profile) {
            return ParserBuilder.opt(new PredicateOrNotParser(profile));
         }
      };
   }

}
