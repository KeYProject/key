package org.key_project.jmlediting.profile.key.locset;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.JMLRefParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.primary.JMLPrimaryKeywordSort;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;

/**
 * Implementation of the reachLocs keyword.
 *
 * @author Moritz Lichter
 *
 */
public class ReachLocsKeyword extends AbstractKeyword {

   /**
    * Creates a new instance.
    */
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
            // Modification: allow an expression is first position
            final ExpressionParser expr = new ExpressionParser(profile);
            return brackets(seq(expr, constant(","), expr,
                  opt(seq(constant(","), expr))));
         }
      };
   }

   @Override
   public IKeywordSort getSort() {
      return JMLPrimaryKeywordSort.INSTANCE;
   }

}
