package org.key_project.jmlediting.profile.key.bounded_quantifier;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;

/**
 * The \bprod keyword.
 * 
 * @author Moritz Lichter
 *
 */
public class BProdQuantifierKeyword extends AbstractEmptyKeyword {

   public BProdQuantifierKeyword() {
      super("\\bprod");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywortSort getSort() {
      return BoundedQuantifierSort.INSTANCE;
   }

}
