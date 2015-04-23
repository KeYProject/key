package org.key_project.jmlediting.profile.jmlref.spec_statement;

import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.parser.JMLRefParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.parser.TargetLabelPredOrNotParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AbstractGenericSpecificationKeyword;

/**
 * Implementation of the break clause keyword.
 *
 * @author Moritz Lichter
 *
 */
public class BreakClauseKeyword extends AbstractGenericSpecificationKeyword {

   /**
    * Creates a new instance of the break keyword.
    */
   public BreakClauseKeyword() {
      super("breaks", "breaks_redundantly");
   }

   @Override
   public String getDescription() {
      return "The meaning of the breaks-clause is that if the statement "
            + "that implements the specification statement executes a "
            + "break, then it must break to the given target-label (if "
            + "any), and the given predicate (if any) must hold in the "
            + "state just before the break is executed.";
   }

   @Override
   public IKeywordParser createParser() {
      return JMLRefParseFunctionKeywordParser
            .semicolonClosed(new TargetLabelPredOrNotParser());
   }

}
