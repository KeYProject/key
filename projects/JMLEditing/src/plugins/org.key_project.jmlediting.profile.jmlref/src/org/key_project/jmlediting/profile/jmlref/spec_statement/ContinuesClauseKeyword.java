package org.key_project.jmlediting.profile.jmlref.spec_statement;

import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.parser.JMLRefParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.parser.TargetLabelPredOrNotParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AbstractGenericSpecificationKeyword;

/**
 * Implementation of the continues clause keyword.
 *
 * @author Moritz Lichter
 *
 */
public class ContinuesClauseKeyword extends AbstractGenericSpecificationKeyword {

   /**
    * Creates a new continues clause keyword.
    */
   public ContinuesClauseKeyword() {
      super("continues", "continues_redundantly");
   }

   @Override
   public String getDescription() {
      return "The meaning of the continues-clause is that if the statement that "
            + "implements the specification statement executes a continue, then "
            + "it must continue to the given target-label (if any), and the given "
            + "predicate (if any) must hold in the state just before the continue "
            + "is executed.";
   }

   @Override
   public IKeywordParser createParser() {
      return JMLRefParseFunctionKeywordParser
            .semicolonClosed(new TargetLabelPredOrNotParser());
   }

}
