package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.parser.JMLRefParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.parser.PredicateContentParser;

public class AxiomKeyword extends AbstractGenericSpecificationKeyword {

   public AxiomKeyword() {
      super("axiom");
   }

   @Override
   public String getDescription() {
      return "An axoim clause specifies that a theorem prover should assume "
            + "that the given predicate is true (whenever such an assumption is needed).";
   }

   @Override
   public IKeywordParser createParser() {
      return JMLRefParseFunctionKeywordParser
            .semicolonClosed(new PredicateContentParser());
   }

}
