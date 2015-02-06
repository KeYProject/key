package org.key_project.jmlediting.profile.key.locset;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;
import static org.key_project.jmlediting.core.parser.util.JavaBasicsParser.ident;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.ParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;

public class ReachLocsParser extends AbstractKeyword implements ILocSetKeyword {

   public ReachLocsParser() {
      super("\\reachLocs");
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
             * \reachLocs(⟨Id⟩, ⟨Expr⟩ (􏰀, ⟨IntExpr⟩􏰁)? )
             */
            final ExpressionParser expr = new ExpressionParser(profile);
            return brackets(seq(ident(), constant(","), expr,
                  opt(seq(constant(","), expr))));
         }
      };
   }

}
