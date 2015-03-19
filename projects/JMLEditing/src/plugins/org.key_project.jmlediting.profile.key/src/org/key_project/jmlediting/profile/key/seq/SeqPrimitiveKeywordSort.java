package org.key_project.jmlediting.profile.key.seq;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeywordSort;

/**
 * This sort specifies keywords which defines seqs.
 *
 * @author Moritz Lichter
 *
 */
public final class SeqPrimitiveKeywordSort extends AbstractKeywordSort {

   /**
    * The shared Sort instance.
    */
   public static final SeqPrimitiveKeywordSort INSTANCE = new SeqPrimitiveKeywordSort();

   /**
    * No other instances.
    */
   private SeqPrimitiveKeywordSort() {
      super("Seq Primitive");
   }

}
