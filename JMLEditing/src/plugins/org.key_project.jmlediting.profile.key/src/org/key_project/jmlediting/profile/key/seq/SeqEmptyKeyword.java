package org.key_project.jmlediting.profile.key.seq;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;

/**
 * The seq empty keyword for key.
 *
 * @author Moritz Lichter
 *
 */
public class SeqEmptyKeyword extends AbstractEmptyKeyword {

   /**
    * Creates a new seq empty keyword.
    */
   public SeqEmptyKeyword() {
      super("\\seq_empty");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywordSort getSort() {
      return SeqPrimitiveKeywordSort.INSTANCE;
   }

}
