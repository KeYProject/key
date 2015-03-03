package org.key_project.jmlediting.profile.key.locset;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;

public class SetMinusOperatorKeyword extends AbstractEmptyKeyword {

   public SetMinusOperatorKeyword() {
      super("\\set_minus");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywortSort getSort() {
      return LocSetOperatorKeywordSort.INSTANCE;
   }

}
