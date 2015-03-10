package org.key_project.jmlediting.profile.key.seq;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;
import static org.key_project.jmlediting.core.parser.util.JavaBasicsParser.ident;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;

public class SeqExpressionParser implements ParseFunction {

   private final ParseFunction seqExprParser;

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return this.seqExprParser.parse(text, start, end);
   }

   public SeqExpressionParser(final IJMLProfile profile) {
      /**
       * seq-expr ::= <br>
       * \seq_empty | <br>
       * \seq_singleton ( expr ) | <br>
       * \values | <br>
       * \seq_concat ( seq-expr , seq-expr ) | <br>
       * seq-expr [ expr .. expr ] | <br>
       * gen-expr | <br>
       * (\seq_def type id ; expr ; expr ; expr )
       *
       */
      // need to rewrite this grammar to avoid infinite recursion
      /**
       *
       * seq-prim ::= <br>
       * \seq_empty |<br>
       * \seq_singleton ( expr ) | <br>
       * \values | <br>
       * \seq_concat ( seq-expr , seq-expr ) |<br>
       * (\seq_def type id ; expr ; expr; expr)
       *
       * seq-suffix ::= '[' expr .. expr ']'
       *
       * seq-expr ::= seq-prim seq-suffix
       *
       *
       */

      final ExpressionParser expr = new ExpressionParser(profile);

      final ParseFunction seqDefExpr = seq(brackets(seq(
            keywords(SeqDefKeyword.class, profile), expr.typeSpec(), ident(),
            separateBy(';', expr), separateBy(';', expr), separateBy(';', expr))));

      final ParseFunction seqPrim = alt(
            keywords(SeqPrimitiveKeywordSort.INSTANCE, profile), seqDefExpr);

      final ParseFunction seqExpr = seqPrim; // , list(seqSuffix));

      this.seqExprParser = seqExpr;
   }

   public static ParseFunction seqSuffix(final IJMLProfile profile) {
      final ExpressionParser expr = new ExpressionParser(profile);
      final ParseFunction seqSuffix = seq(squareBrackets(seq(expr,
            constant(".."), expr)));
      return seqSuffix;
   }

}
