package org.key_project.jmlediting.profile.key.seq;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;
import static org.key_project.jmlediting.core.parser.util.JavaBasicsParser.ident;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.IRecursiveParseFunction;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IJMLPrimary;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;

public class SeqPrimary implements IJMLPrimary {

   private ParseFunction seqExprParser;

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return this.seqExprParser.parse(text, start, end);
   }

   @Override
   public void setProfile(final IJMLProfile profile) {
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
      final IRecursiveParseFunction seqExpr = recursiveInit();
      final ExpressionParser expr = new ExpressionParser(profile);

      final ParseFunction seqExprCase1 = keywords(SeqPrimitiveKeyword.class,
            profile);

      final ParseFunction seqExprCase2 = seq(seqExpr,
            squareBrackets(seq(expr, constant(".."), expr)));

      final ParseFunction seqExprCase3 = seq(
            expr,
            brackets(seq(keywords(SeqDefKeyword.class, profile),
                  expr.typeSpec(), ident(), separateBy(';', expr),
                  separateBy(';', expr), separateBy(';', expr))));

      seqExpr.defineAs(alt(seqExprCase1, seqExprCase2, seqExprCase3));

      this.seqExprParser = seqExpr;
   }
}
