package org.key_project.jmlediting.profile.key.locset;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;

public class IntersetOperatorKeyword extends AbstractEmptyKeyword {

   public IntersetOperatorKeyword() {
      super("\\intersect");
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
