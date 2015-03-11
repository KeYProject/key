package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.SemicolonClosedKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.NothingKeyword;

/**
 * Implementation of the signals_only keyword.
 *
 * @author Moritz Lichter
 *
 */
public class SignalsOnlyKeyword extends AbstractGenericSpecificationKeyword {

   /**
    * New instance of keyword.
    */
   public SignalsOnlyKeyword() {
      super("signals_only", "signals_only_redundantly");
   }

   @Override
   public String getDescription() {
      return "A signals_only clause is an abbreviation for a signals-clause "
            + "that specifies what exceptions may be thrown by a method, "
            + "and thus, implicitly, what exceptions may not be thrown.";
   }

   @Override
   public IKeywordParser createParser() {
      /**
       * signals-only-clause ::= <br>
       * signals-only-keyword reference-type [ , reference-type ] ... ; <br>
       * | signals-only-keyword \nothing ;
       *
       * signals-only-keyword ::= signals_only | signals_only_redundantly
       */
      return new SemicolonClosedKeywordParser() {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLExpressionProfile profile) {
            final ExpressionParser expr = new ExpressionParser(profile);
            return alt(
                  keywords(NothingKeyword.class, profile),
                  separatedNonEmptyList(',', expr.referenceType(),
                        "Expected an Exception type"));
         }
      };
   }

}
