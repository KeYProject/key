package org.key_project.jmlediting.profile.key.locset;

import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;
import org.key_project.jmlediting.profile.jmlref.primary.JMLPrimaryKeywordSort;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.EverythingKeyword;

public class LocSetEverythingKeyword extends EverythingKeyword {

   @Override
   public IKeywortSort getSort() {
      return JMLPrimaryKeywordSort.INSTANCE;
   }

}
