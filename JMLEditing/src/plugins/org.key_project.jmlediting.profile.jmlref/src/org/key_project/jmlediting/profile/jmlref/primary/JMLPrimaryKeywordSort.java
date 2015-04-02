package org.key_project.jmlediting.profile.jmlref.primary;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeywordSort;

/**
 * The sort of a keyword which introduces a JML primary expression.
 *
 * @author Moritz Lichter
 *
 */
public final class JMLPrimaryKeywordSort extends AbstractKeywordSort {

   /**
    * Shared instance of {@link JMLPrimaryKeywordSort} to use.
    */
   public static final JMLPrimaryKeywordSort INSTANCE = new JMLPrimaryKeywordSort();

   /**
    * Only one private instance.
    */
   private JMLPrimaryKeywordSort() {
      super("Primary Keyword");
   }

}
