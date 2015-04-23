package org.key_project.jmlediting.core.profile.syntax;

import java.util.Set;

public abstract class AbstractToplevelKeyword extends AbstractKeyword {

   public AbstractToplevelKeyword(final Set<String> keywords) {
      super(keywords);
   }

   public AbstractToplevelKeyword(final String keyword,
         final String... keywords) {
      super(keyword, keywords);
   }

   @Override
   public IKeywordSort getSort() {
      return ToplevelKeywordSort.INSTANCE;
   }

}
