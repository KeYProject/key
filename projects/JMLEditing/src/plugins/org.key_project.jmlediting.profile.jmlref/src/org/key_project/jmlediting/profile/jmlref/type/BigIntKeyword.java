package org.key_project.jmlediting.profile.jmlref.type;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;

/**
 * Implementation of the bigint keyword.
 *
 * @author Moritz Lichter
 *
 */
public class BigIntKeyword extends AbstractEmptyKeyword {

   /**
    * New instance of bigint keyword.
    */
   public BigIntKeyword() {
      super("\\bigint");
   }

   @Override
   public String getDescription() {
      return "The type \\bigint models arbitrary precision integers. "
            + "However, note that arithmetic does not wrap around, this "
            + "for all values i of type \\bigint, i < i+1.";
   }

   @Override
   public IKeywortSort getSort() {
      return TypeKeywordSort.INSTANCE;
   }

}
