package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.util.JavaBasicsParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.SemicolonClosedKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.PredicateOrNotParser;

/**
 * Implementation of the signals keywords.
 *
 * @author Moritz Lichter
 *
 */
public class SignalsKeyword extends AbstractGenericSpecificationKeyword {

   /**
    * New instance.
    */
   public SignalsKeyword() {
      super("signals", "signals_redundantly", "exsures", "exsures_redundantly");
   }

   @Override
   public String getDescription() {
      return "In a specification case a signals clause specifies "
            + "the exceptional or abnormal postcondition.";
   }

   @Override
   public IKeywordParser createParser() {
      /**
       * signals-clause ::= <br>
       * signals-keyword ( reference-type [ ident ] ) [ pred-or-not ] ;<br>
       *
       * signals-keyword ::= signals | signals_redundantly | exsures |
       * exsures_redundantly
       */
      return new SemicolonClosedKeywordParser() {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLExpressionProfile profile) {
            final PredicateOrNotParser predOrNot = new PredicateOrNotParser(
                  profile);
            final ExpressionParser expr = new ExpressionParser(profile);
            return seq(
                  brackets(seq(expr.referenceType(),
                        opt(JavaBasicsParser.ident()))), opt(predOrNot));
         }
      };
   }

}
