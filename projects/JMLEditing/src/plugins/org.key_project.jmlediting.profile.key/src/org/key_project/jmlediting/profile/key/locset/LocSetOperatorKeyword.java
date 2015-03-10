package org.key_project.jmlediting.profile.key.locset;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;
import org.key_project.jmlediting.core.profile.syntax.JMLPrimaryKeywordSort;
import org.key_project.jmlediting.profile.jmlref.parser.BinarySpecExpressionParser;

public abstract class LocSetOperatorKeyword extends AbstractKeyword {

   public LocSetOperatorKeyword(final String keyword, final String... keywords) {
      super(keyword, keywords);
   }

   @Override
   public IKeywortSort getSort() {
      return JMLPrimaryKeywordSort.INSTANCE;
   }

   @Override
   public IKeywordParser createParser() {
      return new BinarySpecExpressionParser();
   }

}
