package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.SemicolonClosedKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.PredicateParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.SpecExpressionParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.NotSpecifiedKeyword;

/**
 * Implementation for the mesaured_by keyword.
 *
 * @author Moritz Lichter
 *
 */
public class MeasuredByKeyword extends AbstractGenericSpecificationKeyword {

   /**
    * Creates a new instance of the keyword.
    */
   public MeasuredByKeyword() {
      super("measured_by", "measured_by_redundantly");
   }

   @Override
   public String getDescription() {
      return "A measured by clause can be used in a termination "
            + "argument for a recursive specification.";
   }

   @Override
   public IKeywordParser createParser() {
      /**
       * measured-clause ::= <br>
       * measured-by-keyword \not_specified ;<br>
       * | measured-by-keyword spec-expression [ if predicate ] ;<br>
       *
       * measured-by-keyword ::= measured_by | measured_by_redundantly
       */
      return new SemicolonClosedKeywordParser() {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLExpressionProfile profile) {
            final SpecExpressionParser spec = new SpecExpressionParser(profile);
            final PredicateParser predicate = new PredicateParser(profile);
            return alt(keywords(NotSpecifiedKeyword.class, profile),
                  seq(spec, opt(seq(constant("if"), predicate))));
         }
      };
   }

}
