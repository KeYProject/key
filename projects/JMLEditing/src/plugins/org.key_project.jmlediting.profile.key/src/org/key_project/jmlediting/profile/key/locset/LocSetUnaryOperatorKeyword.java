package org.key_project.jmlediting.profile.key.locset;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;
import org.key_project.jmlediting.core.profile.syntax.JMLPrimaryKeywordSort;
import org.key_project.jmlediting.profile.jmlref.parser.BracketSpecExpressionParser;

public abstract class LocSetUnaryOperatorKeyword extends AbstractKeyword {

   public LocSetUnaryOperatorKeyword(final String keyword,
         final String... keywords) {
      super(keyword, keywords);
   }

   @Override
   public IKeywortSort getSort() {
      return JMLPrimaryKeywordSort.INSTANCE;
   }

   @Override
   public IKeywordParser createParser() {
      return new BracketSpecExpressionParser();
   }

}
