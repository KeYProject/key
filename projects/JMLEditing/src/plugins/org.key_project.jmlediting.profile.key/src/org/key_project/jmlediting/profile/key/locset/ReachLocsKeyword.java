package org.key_project.jmlediting.profile.key.locset;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;
import static org.key_project.jmlediting.core.parser.util.JavaBasicsParser.ident;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.JMLRefParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.primary.JMLPrimaryKeywordSort;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;

public class ReachLocsKeyword extends AbstractKeyword {

   public ReachLocsKeyword() {
      super("\\reachLocs");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywordParser createParser() {
      return new JMLRefParseFunctionKeywordParser() {

         @Override
         protected ParseFunction createParseFunction(
               final IJMLExpressionProfile profile) {
            /**
             * \reachLocs( id, expr [, int-expr])
             */
            final ExpressionParser expr = new ExpressionParser(profile);
            return brackets(seq(ident(), constant(","), expr,
                  opt(seq(constant(","), expr))));
         }
      };
   }

   @Override
   public IKeywortSort getSort() {
      return JMLPrimaryKeywordSort.INSTANCE;
   }

}
