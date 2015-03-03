package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeywordSort;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AssignableKeyword;

/**
 * The {@link IStoreRefKeyword} is a sort for keywords which specifies a storage
 * location and is thus used for example in an {@link AssignableKeyword}. All
 * classes which implement this interface are allowed to occur as a storage
 * location.
 *
 * @author Moritz Lichter
 * @see StoreRefListParser
 *
 */
public final class StoreRefKeywordSort extends AbstractKeywordSort {

   /**
    * The shared sort instance.
    */
   public static final StoreRefKeywordSort INSTANCE = new StoreRefKeywordSort();

   /**
    * No other instances.
    */
   private StoreRefKeywordSort() {
      super("Storage reference");
   }

}
