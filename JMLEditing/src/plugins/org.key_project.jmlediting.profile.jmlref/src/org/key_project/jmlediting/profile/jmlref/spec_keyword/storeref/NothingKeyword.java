package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;

/**
 * The \nothing keyword.
 *
 * @author Moritz Lichter
 *
 */
public class NothingKeyword extends AbstractEmptyKeyword {

   /**
    * A new instance for the \nothing keyword.
    */
   public NothingKeyword() {
      super("\\nothing");
   }

   @Override
   public String getDescription() {
      return "Specifies that a method cannot assign to any locations.";
   }

   @Override
   public IKeywordSort getSort() {
      return StoreRefKeywordSort.INSTANCE;
   }
}
