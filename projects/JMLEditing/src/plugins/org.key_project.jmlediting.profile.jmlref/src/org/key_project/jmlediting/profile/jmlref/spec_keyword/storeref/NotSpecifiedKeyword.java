package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;

/**
 * The \not_specified keyword.
 *
 * @author Moritz Lichter
 *
 */
public class NotSpecifiedKeyword extends AbstractEmptyKeyword {

   /**
    * Creates a new instance for the \not_specified keyword.
    */
   public NotSpecifiedKeyword() {
      super("\\not_specified");
   }

   @Override
   public String getDescription() {
      return "The form \\not_specified denotes a unspecified set of locations, "
            + "whose usage is determined by a particular tool";
   }

   @Override
   public IKeywordSort getSort() {
      return StoreRefKeywordSort.INSTANCE;
   }

}
