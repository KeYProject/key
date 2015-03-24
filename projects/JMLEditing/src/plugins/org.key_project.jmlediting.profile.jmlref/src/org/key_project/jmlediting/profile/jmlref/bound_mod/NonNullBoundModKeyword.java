package org.key_project.jmlediting.profile.jmlref.bound_mod;

import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.IKeywordValidator;

/**
 * Non null as bound modifier.
 *
 * @author Moritz Lichter
 *
 */
public class NonNullBoundModKeyword extends AbstractEmptyKeyword {

   /**
    * Creates a new instance.
    */
   public NonNullBoundModKeyword() {
      super("non_null");
   }

   @Override
   public String getDescription() {
      return "Specifies that a bound logical variable is not allowed to be null.\n"
            + "In order to quantify over the elements of a type named non_null or "
            + "nullable is necessary to provide an explicit nullity modifier.";
   }

   @Override
   public IKeywordSort getSort() {
      return BoundVarModifierKeywordSort.INSTANCE;
   }

   @Override
   public IKeywordValidator getKeywordValidator() {
      return null;
   }

}
