package org.key_project.jmlediting.profile.key.other;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.JMLRefParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.primary.ReachKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;

/**
 * KeY modification for the {@link ReachKeyword} which has another arity.
 *
 * @author Moritz Lichter
 *
 */
public class KeYReachKeyword extends ReachKeyword {

   @Override
   public IKeywordParser createParser() {
      return new JMLRefParseFunctionKeywordParser() {

         @Override
         protected ParseFunction createParseFunction(
               final IJMLExpressionProfile profile) {
            /**
             * \reach( id, expr, expr [, int-expr])
             */
            // Modification: allow an expression is first position
            final ExpressionParser expr = new ExpressionParser(profile);
            return brackets(seq(expr, constant(","), expr, constant(","), expr,
                  opt(seq(constant(","), expr))));
         }
      };
   }

}
