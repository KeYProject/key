package org.key_project.jmlediting.profile.key.seq;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;

/**
 * The values keyword for KeY.
 *
 * @author Moritz Lichter
 *
 */
public class ValuesKeyword extends AbstractEmptyKeyword {

   /**
    * Creates a new values keyword instance.
    */
   public ValuesKeyword() {
      super("\\values");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywortSort getSort() {
      return SeqPrimitiveKeywordSort.INSTANCE;
   }

}
