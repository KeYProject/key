package org.key_project.jmlediting.profile.key.other;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;
import static org.key_project.jmlediting.core.parser.util.JavaBasicsParser.ident;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.SemicolonClosedKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AccessibleKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefKeywordSort;

/**
 * Overrides the content of the accessible keyword to contains key specific
 * content.
 *
 * @author Moritz Lichter
 *
 */
public class KeYAccessibleKeyword extends AccessibleKeyword {

   @Override
   public IKeywordParser createParser() {
      return new SemicolonClosedKeywordParser() {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLExpressionProfile profile) {
            final ExpressionParser expr = new ExpressionParser(profile);
            final ParseFunction measuredBy = seq(
                  keywords(AccessibleMeasuredByKeyword.class, profile),
                  expr.exprList());
            final ParseFunction content = alt(
                  keywords(StoreRefKeywordSort.INSTANCE, profile),
                  seq(expr.exprList(), opt(measuredBy)));
            final ParseFunction identAccess = seq(
                  alt(ident(), keywords(InvKeyword.class, profile)),
                  constant(":"), content);
            return alt(identAccess, content);
         }

      };
   }
}
