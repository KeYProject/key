package org.key_project.jmlediting.profile.key.bounded_quantifier;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;

/**
 * The \bsum keyword.
 *
 * @author Moritz Lichter
 *
 */
public class BSumQuantifierKeyword extends AbstractEmptyKeyword {

   public BSumQuantifierKeyword() {
      super("\\bsum");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywordSort getSort() {
      return BoundedQuantifierSort.INSTANCE;
   }

}
