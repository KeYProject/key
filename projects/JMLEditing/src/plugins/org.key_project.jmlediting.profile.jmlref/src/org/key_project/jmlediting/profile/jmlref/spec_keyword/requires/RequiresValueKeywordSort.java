package org.key_project.jmlediting.profile.jmlref.spec_keyword.requires;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeywordSort;

/**
 * A sort which specifies keywords, which can occur as special value in a
 * requires clause: \same and \not_specified.
 *
 * @author Moritz Lichter
 *
 */
public final class RequiresValueKeywordSort extends AbstractKeywordSort {

   /**
    * The shared sort instance.
    */
   public static final RequiresValueKeywordSort INSTANCE = new RequiresValueKeywordSort();

   /**
    * No other instances.
    */
   private RequiresValueKeywordSort() {
      super("Requires value");
   }

}
