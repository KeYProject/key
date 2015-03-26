package org.key_project.jmlediting.core.profile.syntax;

public abstract class AbstractEmptyToplevelKeyword extends AbstractEmptyKeyword {

   public AbstractEmptyToplevelKeyword(final String keyword,
         final String... keywords) {
      super(keyword, keywords);
   }

   @Override
   public IKeywordSort getSort() {
      return ToplevelKeywordSort.INSTANCE;
   }

}
