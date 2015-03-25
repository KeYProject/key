package org.key_project.jmlediting.profile.key.other;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefKeywordSort;

/**
 * Key specific less than nothing keyword as an additional store ref keyword.
 *
 * @author Moritz Lichter
 *
 */
public class LessThanNothingKeyword extends AbstractEmptyKeyword {

   /**
    * New instance of the keyword.
    */
   public LessThanNothingKeyword() {
      super("\\less_than_nothing");
   }

   @Override
   public IKeywordSort getSort() {
      return StoreRefKeywordSort.INSTANCE;
   }

   @Override
   public String getDescription() {
      return null;
   }

}
