package org.key_project.jmlediting.profile.key.seq;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.profile.jmlref.primary.JMLPrimaryKeywordSort;

/**
 * Implementation of the \index keyword.
 *
 * @author Moritz Lichter
 *
 */
public class IndexKeyword extends AbstractEmptyKeyword {

   /**
    * New index keyword.
    */
   public IndexKeyword() {
      super("\\index");
   }

   @Override
   public IKeywordSort getSort() {
      return JMLPrimaryKeywordSort.INSTANCE;
   }

   @Override
   public String getDescription() {
      return null;
   }

}
