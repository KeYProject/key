package org.key_project.jmlediting.profile.jmlref.quantifier;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeywordSort;

/**
 * This sort specifies a keywords which can be used in as a keyword for a
 * quantifier. Quantifier keywords needs to implement this interface.
 *
 * @author Moritz Lichter
 *
 */
public final class QuantifierKeywordSort extends AbstractKeywordSort {

   /**
    * The shared instance for use.
    */
   public static final QuantifierKeywordSort INSTANCE = new QuantifierKeywordSort();

   /**
    * No other instances.
    */
   private QuantifierKeywordSort() {
      super("Quantifier");
   }

}
