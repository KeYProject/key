package org.key_project.jmlediting.profile.jmlref.model;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;
import static org.key_project.jmlediting.core.parser.util.JavaBasicsParser.ident;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.syntax.AbstractToplevelKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.SemicolonClosedKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;

/**
 * An implementation of a keyword which allows the declaration of a variable
 * behind it.
 *
 * @author Moritz Lichter
 *
 */
public abstract class VariableDeclarationKeyword extends
      AbstractToplevelKeyword {

   /**
    * Creates a new {@link VariableDeclarationKeyword}.
    *
    * @param keyword
    *           the first introducing keyword.
    * @param keywords
    *           optional others
    */
   public VariableDeclarationKeyword(final String keyword,
         final String... keywords) {
      super(keyword, keywords);
   }

   @Override
   public IKeywordParser createParser() {
      return new SemicolonClosedKeywordParser() {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLExpressionProfile profile) {
            final ExpressionParser expr = new ExpressionParser(profile);

            return seq(
                  expr.typeSpec(),
                  separatedNonEmptyListErrorRecovery(',', ident(),
                        "Expected at least one variable name"),
                  opt(seq(constant("="), expr)));
         }
      };
   }

}
