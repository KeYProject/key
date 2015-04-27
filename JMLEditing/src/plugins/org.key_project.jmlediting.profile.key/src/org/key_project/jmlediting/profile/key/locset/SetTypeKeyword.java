package org.key_project.jmlediting.profile.key.locset;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.profile.jmlref.type.TypeKeywordSort;

/**
 * The seq type keyword defined in KeY. It is registered as a new type.
 *
 * @author Moritz Lichter
 *
 */
public class SetTypeKeyword extends AbstractEmptyKeyword {

   /**
    * Creates a new seq keyword instance.
    */
   public SetTypeKeyword() {
      super("\\set");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywordSort getSort() {
      return TypeKeywordSort.INSTANCE;
   }

}
