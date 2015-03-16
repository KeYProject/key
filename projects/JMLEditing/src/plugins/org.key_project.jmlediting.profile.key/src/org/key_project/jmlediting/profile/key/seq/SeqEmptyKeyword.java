package org.key_project.jmlediting.profile.key.seq;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;

public class SeqEmptyKeyword extends AbstractEmptyKeyword {

   public SeqEmptyKeyword() {
      super("\\seq_empty");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywortSort getSort() {
      return SeqPrimitiveKeywordSort.INSTANCE;
   }

}
