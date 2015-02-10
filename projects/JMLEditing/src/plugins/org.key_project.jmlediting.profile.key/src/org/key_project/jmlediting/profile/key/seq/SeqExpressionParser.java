package org.key_project.jmlediting.profile.key.seq;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;
import static org.key_project.jmlediting.core.parser.util.JavaBasicsParser.ident;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;

public class SeqExpressionParser implements ParseFunction {

   public static final ParseFunction seqExpressionSuffix(
         final IJMLProfile profile) {
      final ExpressionParser expr = new ExpressionParser(profile);
      final ParseFunction seqExpressionSuffix = brackets(seq(
            keywords(SeqDefKeyword.class, profile), expr.typeSpec(), ident(),
            separateBy(';', expr), separateBy(';', expr), separateBy(';', expr)));
      return seqExpressionSuffix;
   }

   private final ParseFunction seqExprParser;

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return this.seqExprParser.parse(text, start, end);
   }

   public SeqExpressionParser(final IJMLProfile profile) {
      /**
       * seq-expr ::= <br>
       * \seq_empty | (1)<br>
       * \seq_singleton ( expr ) | (1) <br>
       * \values | (1)<br>
       * \seq_concat ( seq-expr , seq-expr ) | (1)<br>
       * seq-expr [ expr .. expr ] (2) | <br>
       * expr ( \seq_def type id ; expr ; expr ; expr ) (3)
       *
       */
      // need to rewrite this grammar to avoid infinite recursion
      /**
       * seq-prim ::= <br>
       * \seq_empty |<br>
       * \seq_singleton ( expr ) | <br>
       * \values | <br>
       * \seq_concat ( seq-expr , seq-expr )<br>
       *
       * seq-suffix ::= '[' expr .. expr ']' seq-expr ::= seq-prim seq-suffix
       *
       * condition-expression-suffix = ( \seq_def type id ; expr ; expr ; expr )
       * |<br>
       * conditional-expression-suffix
       *
       */
      // the suffix is creates by the static function in this class and
      // registered in the key profile

      // final IRecursiveParseFunction seqExpr = recursiveInit();
      final ExpressionParser expr = new ExpressionParser(profile);

      final ParseFunction seqSuffix = seq(squareBrackets(seq(expr,
            constant(".."), expr)));

      final ParseFunction seqPrim = alt(keywords(SeqPrimitiveKeyword.class,
            profile));
      final ParseFunction seqExpr = seq(seqPrim, list(seqSuffix));

      this.seqExprParser = seqExpr;
   }

}
