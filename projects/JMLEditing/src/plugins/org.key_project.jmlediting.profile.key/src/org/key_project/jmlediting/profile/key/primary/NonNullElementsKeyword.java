package org.key_project.jmlediting.profile.key.primary;

import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.parser.SpecExpressionListArgParser;
import org.key_project.jmlediting.profile.jmlref.primary.AbstractJMLPrimaryKeyword;

public class NonNullElementsKeyword extends AbstractJMLPrimaryKeyword {

   public NonNullElementsKeyword() {
      super("\\nonnullelements");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywordParser createParser() {
      return new SpecExpressionListArgParser();
   }

}
