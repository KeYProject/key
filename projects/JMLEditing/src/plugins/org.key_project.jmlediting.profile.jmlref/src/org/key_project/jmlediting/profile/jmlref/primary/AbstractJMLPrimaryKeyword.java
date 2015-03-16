package org.key_project.jmlediting.profile.jmlref.primary;

import java.util.Set;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;

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
