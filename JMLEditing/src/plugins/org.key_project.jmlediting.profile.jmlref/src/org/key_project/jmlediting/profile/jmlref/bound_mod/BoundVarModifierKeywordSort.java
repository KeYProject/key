package org.key_project.jmlediting.profile.jmlref.bound_mod;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeywordSort;

/**
 * The sort for keywords of bound variables modifiers.
 *
 * @author Moritz Lichter
 *
 */
public final class BoundVarModifierKeywordSort extends AbstractKeywordSort {

   /**
    * The shared instance.
    */
   public static final BoundVarModifierKeywordSort INSTANCE = new BoundVarModifierKeywordSort();

   /**
    * Only one shared instance.
    */
   private BoundVarModifierKeywordSort() {
      super("Bound variable modifier");
   }

}
