package org.key_project.jmlediting.profile.key.locset;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeywordSort;

/**
 * This sort specifies keywords which creates in a location set.
 *
 * @author Moritz Lichter
 *
 */
public final class LocSetKeywordSort extends AbstractKeywordSort {

   /**
    * The shared sort instance.
    */
   public static final LocSetKeywordSort INSTANCE = new LocSetKeywordSort();

   /**
    * No other instances.
    */
   private LocSetKeywordSort() {
      super("Location Set");
   }
}
