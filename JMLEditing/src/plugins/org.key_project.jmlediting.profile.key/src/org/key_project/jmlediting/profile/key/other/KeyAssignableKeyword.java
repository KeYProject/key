package org.key_project.jmlediting.profile.key.other;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.SemicolonClosedKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AssignableKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefKeywordSort;

/**
 * Overrides the content of the JML Reference keyword to support expressions.
 * 
 * @author Moritz Lichter
 *
 */
public class KeYAssignableKeyword extends AssignableKeyword {

   @Override
   public IKeywordParser createParser() {
      return new SemicolonClosedKeywordParser() {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLExpressionProfile profile) {
            final ExpressionParser expr = new ExpressionParser(profile);
            return alt(keywords(StoreRefKeywordSort.INSTANCE, profile),
                  expr.exprList());
         }
      };
   }
}
