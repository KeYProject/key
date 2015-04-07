package org.key_project.jmlediting.profile.key.spec_statement;

import static org.key_project.jmlediting.profile.jmlref.parser.JMLRefParseFunctionKeywordParser.semicolonClosed;

import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AbstractGenericSpecificationKeyword;
import org.key_project.jmlediting.profile.key.parser.KeYTargetLabelPredicateParser;

public class KeYBreaksClauseKeyword extends AbstractGenericSpecificationKeyword {

   public KeYBreaksClauseKeyword() {
      super("breaks");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywordParser createParser() {
      return semicolonClosed(new KeYTargetLabelPredicateParser());
   }

}
