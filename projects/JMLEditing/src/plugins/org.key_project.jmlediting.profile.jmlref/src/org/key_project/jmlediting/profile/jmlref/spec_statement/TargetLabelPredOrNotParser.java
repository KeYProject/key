package org.key_project.jmlediting.profile.jmlref.spec_statement;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.util.JavaBasicsParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.SemicolonClosedKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.PredicateOrNotParser;

/**
 * Parser for the content of continues and break clauses.
 *
 * @author Moritz Lichter
 *
 */
final class TargetLabelPredOrNotParser extends SemicolonClosedKeywordParser {
   @Override
   protected ParseFunction createContentParseFunction(
         final IJMLExpressionProfile profile) {
      /**
       * continues-clause ::= <br>
       * continues-keyword [ target-label ] [ pred-or-not ] ;<br>
       *
       * continues-keyword ::= continues | continues_redundantly <br>
       * target-label ::= -> ( ident )
       */

      /**
       *
       breaks-clause ::= <br>
       * breaks-keyword [ target-label ] [ pred-or-not ] ;<br>
       * breaks-keyword ::= breaks | breaks_redundantly
       */

      final ParseFunction targetLabel = seq(constant("->"),
            brackets(JavaBasicsParser.ident()));
      final ParseFunction predOrNot = new PredicateOrNotParser(profile);

      return seq(opt(targetLabel), opt(predOrNot));

   }
}