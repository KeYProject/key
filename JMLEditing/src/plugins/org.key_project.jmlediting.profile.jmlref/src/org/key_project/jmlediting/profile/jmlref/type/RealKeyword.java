package org.key_project.jmlediting.profile.jmlref.type;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;

/**
 * Implementation of the real keyword.
 *
 * @author Moritz Lichter
 *
 */
public class RealKeyword extends AbstractEmptyKeyword {

   /**
    * No instance of real.
    */
   public RealKeyword() {
      super("\\real");
   }

   @Override
   public String getDescription() {
      return "The type \real models arbitrary precision floating point numbers.";
   }

   @Override
   public IKeywordSort getSort() {
      return TypeKeywordSort.INSTANCE;
   }

}
