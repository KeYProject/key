package org.key_project.jmlediting.profile.key.locset;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;
import static org.key_project.jmlediting.core.parser.util.JavaBasicsParser.ident;

import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.ParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;

public class InfiniteUnionKeyword extends AbstractKeyword implements
      ILocSetKeyword {

   public InfiniteUnionKeyword() {
      super("\\infinite_union");
   }

   @Override
   public String getDescription() {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public IKeywordParser createParser() {
      return new ParseFunctionKeywordParser() {

         @Override
         protected ParseFunction createParseFunction(final IJMLProfile profile) {
            /**
             * \infinite_union(⟨Type⟩ ⟨Id⟩; 􏰀(⟨BoolExpr⟩;)􏰁? ⟨LocSetExpr⟩)
             */
            final LocSetExprListParser locSetExpr = new LocSetExprListParser(
                  profile);
            final ExpressionParser expr = new ExpressionParser(profile);
            return brackets(seq(expr.typeSpec(), ident(), constant(";"),
                  opt(closedBy(NodeTypes.NODE, expr, ';')), locSetExpr.elem()));
         }
      };
   }

}
