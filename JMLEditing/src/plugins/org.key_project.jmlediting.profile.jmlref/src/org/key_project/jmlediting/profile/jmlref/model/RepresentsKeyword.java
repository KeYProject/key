package org.key_project.jmlediting.profile.jmlref.model;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.syntax.AbstractToplevelKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.SemicolonClosedKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.PredicateParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.SpecExpressionParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefListParser;

/**
 * The implementation of the represents keyword.
 *
 * @author Moritz Lichter
 *
 */
public class RepresentsKeyword extends AbstractToplevelKeyword {

   /**
    * Creates a new instance of the represents keyword.
    */
   public RepresentsKeyword() {
      super("represents");
   }

   @Override
   public String getDescription() {
      return "The first form of represents clauses is called a functional abstraction. "
            + "This form defines the value of the store-ref-expression in a visible "
            + "state as the value of the spec-expression that follows the =. The "
            + "second form (with \\such_that) is called a relational abstraction. "
            + "This form constrains the value of the store-ref-expression in a "
            + "visible state to satisfy the given predicate. ";
   }

   @Override
   public IKeywordParser createParser() {
      return new SemicolonClosedKeywordParser() {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLExpressionProfile profile) {
            final ParseFunction storeRef = new StoreRefListParser(profile,
                  false).storeRef();
            final ParseFunction specExpr = new SpecExpressionParser(profile);
            final ParseFunction predicate = new PredicateParser(profile);
            final ParseFunction suchThat = keywords(SuchThatKeyword.class,
                  profile);

            /**
             * represents-clause ::= <br>
             * represents-keyword store-ref-expression = spec-expression ;<br>
             * | represents-keyword store-ref-expression \such_that predicate ;
             */
            final ParseFunction representsClause = alt(
                  seq(storeRef, constant("="), specExpr),
                  seq(storeRef, suchThat, predicate));

            return representsClause;
         }
      };
   }
}
