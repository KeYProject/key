package org.key_project.jmlediting.profile.key.locset;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.profile.jmlref.parser.BinarySpecExpressionArgParser;
import org.key_project.jmlediting.profile.jmlref.primary.JMLPrimaryKeywordSort;

public abstract class LocSetBinaryOperatorKeyword extends AbstractKeyword {

   public LocSetBinaryOperatorKeyword(final String keyword, final String... keywords) {
      super(keyword, keywords);
   }

   @Override
   public IKeywordSort getSort() {
      return JMLPrimaryKeywordSort.INSTANCE;
   }

   @Override
   public IKeywordParser createParser() {
      return new BinarySpecExpressionArgParser();
   }

}
