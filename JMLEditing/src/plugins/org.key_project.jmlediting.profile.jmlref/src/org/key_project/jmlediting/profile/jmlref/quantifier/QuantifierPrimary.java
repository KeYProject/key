package org.key_project.jmlediting.profile.jmlref.quantifier;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;
import static org.key_project.jmlediting.profile.jmlref.quantifier.QuantifierNodeTypes.*;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.parser.util.JavaBasicsParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.bound_mod.BoundVarModifierKeywordSort;
import org.key_project.jmlediting.profile.jmlref.primary.IJMLPrimary;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.PredicateParser;

/**
 * The implementation of the quantifier primaries of JML. This primary parses
 * any quantifier. The supported quantifiers are defined by the
 * {@link IQuantifierKeyword} available in the JML profile.
 *
 * @author Moritz Lichter
 *
 */
public class QuantifierPrimary implements IJMLPrimary {

   /**
    * The main parser for quantifiers.
    */
   private ParseFunction quantifierParser;
   private ParseFunction quantifiedVarDecls;

   @Override
   public void setProfile(final IJMLExpressionProfile profile) {
      final ExpressionParser expr = new ExpressionParser(profile);
      final PredicateParser predicate = new PredicateParser(profile);

      /**
       * quantifier ::= \forall | \exists<br>
       * | \max | \min<br>
       * | \num_of | \product | \sum
       */
      final ParseFunction quantifier = keywords(QuantifierKeywordSort.INSTANCE,
            profile);

      final ParseFunction boundVarModifier = keywords(
            BoundVarModifierKeywordSort.INSTANCE, profile);
      /**
       * quantified-var-declarator ::= ident [ dims ]
       */
      final ParseFunction quantifiedVarDeclarator = seq(
            JavaBasicsParser.ident(), opt(expr.dims()));

      /**
       * quantified-var-decls ::= <br>
       * [ bound-var-modifiers ] type-spec quantified-var-declarator [ ,
       * quantified-var-declarator ] ...
       */
      final ParseFunction quantifiedVarDecls = seq(
            opt(boundVarModifier),
            expr.typeSpec(),
            separatedNonEmptyList(',', quantifiedVarDeclarator,
                  "Expected a quantified var declarator"));

      /**
       * spec-quantified-expr ::= ( quantifier quantified-var-decls ;<br>
       * [ [ predicate ] ; ]<br>
       * spec-expression )
       */
      final ParseFunction specQuantifiedExpr = brackets(seq(
            QUANTIFIED_EXPRESSION, quantifier, quantifiedVarDecls,
            constant(";"),
            opt(seq(closedBy(QUANTIFIER_PREDICATE, opt(predicate), ';'))), expr));

      this.quantifierParser = specQuantifiedExpr;
      this.quantifiedVarDecls = quantifiedVarDecls;
   }

   public ParseFunction quantifiedVarDecls() {
      return this.quantifiedVarDecls;
   }

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return this.quantifierParser.parse(text, start, end);
   }
}
