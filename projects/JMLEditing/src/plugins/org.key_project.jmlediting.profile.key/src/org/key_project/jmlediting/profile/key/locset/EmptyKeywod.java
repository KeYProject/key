package org.key_project.jmlediting.profile.key.locset;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;
import org.key_project.jmlediting.profile.jmlref.primary.JMLPrimaryKeywordSort;

public class EmptyKeywod extends AbstractEmptyKeyword {

   public EmptyKeywod() {
      super("\\empty");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywortSort getSort() {
      return JMLPrimaryKeywordSort.INSTANCE;
   }

}
