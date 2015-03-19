package org.key_project.jmlediting.profile.key.spec_statement;

import static org.key_project.jmlediting.profile.jmlref.parser.JMLRefParseFunctionKeywordParser.semicolonClosed;

import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AbstractGenericSpecificationKeyword;
import org.key_project.jmlediting.profile.key.parser.KeyTargetLabelPredicateParser;

public class KeyReturnsClauseKeyword extends
      AbstractGenericSpecificationKeyword {

   public KeyReturnsClauseKeyword() {
      super("returns");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywordParser createParser() {
      return semicolonClosed(new KeyTargetLabelPredicateParser());
   }

}
