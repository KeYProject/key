package org.key_project.jmlediting.profile.key.other;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefKeywordSort;

public class StrictlyNothingKeyword extends AbstractEmptyKeyword {

   public StrictlyNothingKeyword() {
      super("\\strictly_nothing");
   }

   @Override
   public String getDescription() {
      return "Specifies that a method cannot assign to any locations.<br> <b> The strictly_nothing disallows the creation of new objects additionally.<br>";
   }

   @Override
   public IKeywortSort getSort() {
      return StoreRefKeywordSort.INSTANCE;
   }

}
