package org.key_project.jmlediting.profile.key.locset;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
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
   public IKeywordSort getSort() {
      return TypeKeywordSort.INSTANCE;
   }

}
