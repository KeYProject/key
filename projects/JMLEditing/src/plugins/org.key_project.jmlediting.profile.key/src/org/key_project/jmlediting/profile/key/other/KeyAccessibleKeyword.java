package org.key_project.jmlediting.profile.key.other;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;
import static org.key_project.jmlediting.core.parser.util.JavaBasicsParser.ident;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AccessibleKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.SemicolonClosedKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefKeywordSort;

public class KeyAccessibleKeyword extends AccessibleKeyword {

   public KeyAccessibleKeyword() {

   }

   @Override
   public IKeywordParser createParser() {
      return new SemicolonClosedKeywordParser() {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLProfile profile) {
            final ExpressionParser expr = new ExpressionParser(profile);
            final ParseFunction content = alt(
                  keywords(StoreRefKeywordSort.INSTANCE, profile),
                  expr.exprList());
            return alt(
                  seq(alt(ident(), keywords(InvKeyword.class, profile)),
                        constant(":"), content), content);
         }

      };
   }
}
