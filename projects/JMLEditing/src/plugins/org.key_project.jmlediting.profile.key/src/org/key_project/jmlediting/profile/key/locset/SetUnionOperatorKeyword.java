package org.key_project.jmlediting.profile.key.locset;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;

public class SetUnionOperatorKeyword extends AbstractEmptyKeyword {

   public SetUnionOperatorKeyword() {
      super("\\set_union");
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
