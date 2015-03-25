package org.key_project.jmlediting.profile.key.other;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefKeywordSort;

/**
 * Strictly nothing keyword which is more strict that the norhing keyword.
 *
 * @author Moritz Lichter
 *
 */
public class StrictlyNothingKeyword extends AbstractEmptyKeyword {

   /**
    * New instance.
    */
   public StrictlyNothingKeyword() {
      super("\\strictly_nothing");
   }

   @Override
   public String getDescription() {
      return "Specifies that a method cannot assign to any"
            + "locations.<br> <b> The strictly_nothing disallows the creation"
            + "of new objects additionally.<br>";
   }

   @Override
   public IKeywordSort getSort() {
      return StoreRefKeywordSort.INSTANCE;
   }

}
