package org.key_project.jmlediting.profile.jmlref.primary;

import java.util.Set;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;

public abstract class AbstractJMLPrimaryKeyword extends AbstractKeyword {

   public AbstractJMLPrimaryKeyword(final Set<String> keywords) {
      super(keywords);
   }

   public AbstractJMLPrimaryKeyword(final String keyword,
         final String... keywords) {
      super(keyword, keywords);
   }

   @Override
   public IKeywordSort getSort() {
      return JMLPrimaryKeywordSort.INSTANCE;
   }

}
