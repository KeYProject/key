package org.key_project.jmlediting.core.profile.syntax;

public abstract class AbstractEmptyToplevelKeyword extends AbstractEmptyKeyword {

   public AbstractEmptyToplevelKeyword(final String keyword,
         final String... keywords) {
      super(keyword, keywords);
      // TODO Auto-generated constructor stub
   }

   @Override
   public IKeywortSort getSort() {
      return ToplevelKeywordSort.INSTANCE;
   }

}
