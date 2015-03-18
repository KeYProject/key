package org.key_project.jmlediting.profile.key.bounded_quantifier;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeywordSort;

/**
 * The sort for all bounded quantifier keywords.
 * 
 * @author Moritz Lichter
 *
 */
public class BoundedQuantifierSort extends AbstractKeywordSort {

   /**
    * The shared instance for use.
    */
   public static final BoundedQuantifierSort INSTANCE = new BoundedQuantifierSort();

   private BoundedQuantifierSort() {
      super("Bounded Quantifier Keyword");
   }

}
