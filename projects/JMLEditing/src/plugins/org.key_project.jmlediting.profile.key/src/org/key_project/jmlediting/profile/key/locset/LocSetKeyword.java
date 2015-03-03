package org.key_project.jmlediting.profile.key.locset;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;
import org.key_project.jmlediting.profile.jmlref.type.TypeKeywordSort;

public class LocSetKeyword extends AbstractEmptyKeyword {

   public LocSetKeyword() {
      super("\\locset");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywortSort getSort() {
      return TypeKeywordSort.INSTANCE;
   }

}
