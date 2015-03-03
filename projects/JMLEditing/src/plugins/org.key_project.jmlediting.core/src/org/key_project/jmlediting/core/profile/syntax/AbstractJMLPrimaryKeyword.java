package org.key_project.jmlediting.core.profile.syntax;

import java.util.Set;

public abstract class AbstractJMLPrimaryKeyword extends AbstractKeyword {

   public AbstractJMLPrimaryKeyword(final Set<String> keywords) {
      super(keywords);
      // TODO Auto-generated constructor stub
   }

   public AbstractJMLPrimaryKeyword(final String keyword,
         final String... keywords) {
      super(keyword, keywords);
      // TODO Auto-generated constructor stub
   }

   @Override
   public IKeywortSort getSort() {
      return JMLPrimaryKeywordSort.INSTANCE;
   }

}
