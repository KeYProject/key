package org.key_project.jmlediting.profile.key.other;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;
import org.key_project.jmlediting.core.profile.syntax.JMLPrimaryKeywordSort;

/**
 * Implementation of the \index keyword.
 * 
 * @author Moritz Lichter
 *
 */
public class IndexKeyword extends AbstractEmptyKeyword {

   public IndexKeyword() {
      super("\\index");
   }

   @Override
   public IKeywortSort getSort() {
      return JMLPrimaryKeywordSort.INSTANCE;
   }

   @Override
   public String getDescription() {
      return null;
   }

}
