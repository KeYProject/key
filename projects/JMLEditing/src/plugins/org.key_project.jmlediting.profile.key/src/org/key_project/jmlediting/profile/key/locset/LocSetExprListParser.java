package org.key_project.jmlediting.profile.key.locset;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.parser.IRecursiveParseFunction;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefListParser;

public class LocSetExprListParser {

   // private final ParseFunction mainParser;
   // private final ParseFunction elem;

   private LocSetExprListParser(final IJMLProfile profile) {
      // TODO Auto-generated method stub
      final ExpressionParser expr = new ExpressionParser(profile);
      final StoreRefListParser storeRef = new StoreRefListParser(profile, false);

      /**
       * loc-set-expr ::=<br>
       * expr . id | <br>
       * expr [ int-expr ] | <br>
       * expr [ int-expr .. int-expr] | <br>
       * expr [*] | <br>
       * expr .* | <br>
       * \empty | <br>
       * \everything | <br>
       * loc-set-op ( loc-set-expr , loc-set-expr) | <br>
       * \inifinite_union ( type id; [bool-expr ;] loc-set-expr) | <br>
       * \reachLocs (id, expr [, int-expr]) | <br>
       * gen-expr
       *
       * loc-set-op ::= \intersect | \set_union | set_minus
       */
      final IRecursiveParseFunction locSetExpr = recursiveInit();
      /*
       * final ParseFunction locSetOp = keywords(
       * LocSetOperatorKeywordSort.INSTANCE, profile); final ParseFunction
       * locSetOpExpr = seq(locSetOp, brackets(seq(locSetExpr, constant(","),
       * locSetExpr)));
       *
       * final ParseFunction otherKeywords =
       * keywords(LocSetKeywordSort.INSTANCE, profile);
       *
       * locSetExpr .defineAs(alt(storeRef.storeRef(), otherKeywords,
       * locSetOpExpr));
       *
       * final ParseFunction locSetExprList = typed( STORE_REF_LIST,
       * alt(keywords(StoreRefKeywordSort.INSTANCE, profile),
       * separatedNonEmptyListErrorRecovery(',', locSetExpr,
       * "Expected a Loc Set Expr")));
       *
       * this.mainParser = locSetExprList; this.elem = locSetExpr;
       */
   }

   public static ParseFunction locSetSuffixes() {
      final ParseFunction arrayAll = seq(constant("["), constant("*"),
            constant("]"));
      final ParseFunction allFields = seq(constant("."), constant("*"));

      return alt(arrayAll, allFields);
   }

}
