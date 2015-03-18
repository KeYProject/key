package org.key_project.jmlediting.profile.key.other;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefKeywordSort;

public class LessThanNothingKeyword extends AbstractEmptyKeyword {
   public LessThanNothingKeyword() {
      super("\\less_than_nothing");
   }

   @Override
   public IKeywortSort getSort() {
      return StoreRefKeywordSort.INSTANCE;
   }

   @Override
   public String getDescription() {
      return null;
   }

}
