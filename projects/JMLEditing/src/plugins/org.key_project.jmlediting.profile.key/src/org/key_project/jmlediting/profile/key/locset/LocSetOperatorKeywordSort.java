package org.key_project.jmlediting.profile.key.locset;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeywordSort;

/**
 * This sort specifies keywords which is a binary operator on location sets.
 *
 * @author Moritz Lichter
 *
 */
public final class LocSetOperatorKeywordSort extends AbstractKeywordSort {

   /**
    * The shared sort instance.
    */
   public static final LocSetOperatorKeywordSort INSTANCE = new LocSetOperatorKeywordSort();

   /**
    * No other instances.
    */
   private LocSetOperatorKeywordSort() {
      super("Location Set Operator");
   }

}
