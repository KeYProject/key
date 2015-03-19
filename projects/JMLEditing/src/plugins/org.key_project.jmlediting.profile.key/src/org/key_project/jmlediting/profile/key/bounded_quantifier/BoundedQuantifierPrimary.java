package org.key_project.jmlediting.profile.key.bounded_quantifier;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;
import static org.key_project.jmlediting.profile.jmlref.quantifier.QuantifierNodeTypes.*;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.primary.IJMLPrimary;
import org.key_project.jmlediting.profile.jmlref.quantifier.QuantifierPrimary;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;

/**
 * The implementation of the bounded quantifier primaries of KeY. This primary
 * parses any bounded quantifier.
 *
 * @author Moritz Lichter
 *
 */
public class BoundedQuantifierPrimary implements IJMLPrimary {

   /**
    * The main parser for quantifiers.
    */
   private ParseFunction quantifierParser;

   @Override
   public void setProfile(final IJMLExpressionProfile profile) {
      // The following syntax is quessed from examples

      final ExpressionParser expr = new ExpressionParser(profile);
      final QuantifierPrimary qPrimary = new QuantifierPrimary();
      qPrimary.setProfile(profile);

      /**
       * bsum-quantifier ::= \bsum | \bprod
       */
      final ParseFunction quantifier = keywords(BoundedQuantifierSort.INSTANCE,
            profile);

      /**
       * bsum-spec-quantified-expr ::= <br>
       * ( quantifier quantified-var-decls ; spec-expression ;spec-expression ;
       * spec-expression )
       */
      final ParseFunction specQuantifiedExpr = brackets(seq(
            QUANTIFIED_EXPRESSION, quantifier, qPrimary.quantifiedVarDecls(),
            constant(";"), closedBy(QUANTIFIER_PREDICATE, expr, ';'),
            closedBy(QUANTIFIER_PREDICATE, expr, ';'), expr));

      this.quantifierParser = specQuantifiedExpr;
   }

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return this.quantifierParser.parse(text, start, end);
   }
}
