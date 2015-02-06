package org.key_project.jmlediting.profile.key.locset;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;
import static org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefNodeTypes.STORE_REF_LIST;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.IRecursiveParseFunction;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.IStoreRefKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefListParser;

public class LocSetExprListParser implements ParseFunction {

   private final ParseFunction mainParser;
   private final ParseFunction elem;

   public LocSetExprListParser(final IJMLProfile profile) {
      // TODO Auto-generated method stub
      final ExpressionParser expr = new ExpressionParser(profile);
      final StoreRefListParser storeRef = new StoreRefListParser(profile, false);

      /**
       * ⟨LocSetExpr⟩ ::=<br>
       * ⟨Expr⟩.⟨Id⟩ <br>
       * | ⟨Expr⟩[⟨IntExpr⟩] <br>
       * | ⟨Expr⟩[⟨IntExpr⟩..⟨IntExpr⟩]<br>
       * | ⟨Expr⟩[*] <br>
       * | ⟨Expr⟩.*<br>
       * | \empty <br>
       * | \everything<br>
       * | ⟨LocSetOp⟩(⟨LocSetExpr⟩, ⟨LocSetExpr⟩) <br>
       * | \infinite_union(⟨Type⟩ ⟨Id⟩; 􏰀⟨BoolExpr⟩; 􏰁?⟨LocSetExpr⟩) <br>
       * | \reachLocs(⟨Id⟩, ⟨Expr⟩􏰀, ⟨IntExpr⟩􏰁?) <br>
       * | ⟨GenExpr⟩<br>
       * <br>
       * ⟨LocSetOp⟩ ::= \intersect | \set_union | \set_minus
       */
      final IRecursiveParseFunction locSetExpr = recursiveInit();

      final ParseFunction locSetOp = keywords(ILocSetOperatorKeyword.class,
            profile);
      final ParseFunction locSetOpExpr = seq(locSetOp,
            brackets(seq(locSetExpr, constant(","), locSetExpr)));

      final ParseFunction otherKeywords = keywords(ILocSetKeyword.class,
            profile);

      locSetExpr
            .defineAs(alt(storeRef.storeRef(), otherKeywords, locSetOpExpr));

      final ParseFunction locSetExprList = typed(
            STORE_REF_LIST,
            alt(keywords(IStoreRefKeyword.class, profile),
                  separatedNonEmptyListErrorRecovery(',', locSetExpr,
                        "Expected a Loc Set Expr")));

      this.mainParser = locSetExprList;
      this.elem = locSetExpr;
   }

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return this.mainParser.parse(text, start, end);
   }

   public ParseFunction elem() {
      return this.elem;
   }

}
