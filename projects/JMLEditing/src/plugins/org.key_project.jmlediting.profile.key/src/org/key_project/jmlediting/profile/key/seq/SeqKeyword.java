package org.key_project.jmlediting.profile.key.seq;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;
import org.key_project.jmlediting.profile.jmlref.type.TypeKeywordSort;

/**
 * The seq type keyword defined in KeY. It is registered as a new type.
 *
 * @author Moritz Lichter
 *
 */
public class SeqKeyword extends AbstractEmptyKeyword {

   /**
    * Creates a new seq keyword instance.
    */
   public SeqKeyword() {
      super("\\seq");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywortSort getSort() {
      return TypeKeywordSort.INSTANCE;
   }

}
