package org.key_project.jmlediting.profile.jmlref.type;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeywordSort;

/**
 * A keyword which defines a custom type available in JML expressions.
 *
 * @author Moritz Lichter
 *
 */
public final class TypeKeywordSort extends AbstractKeywordSort {

   /**
    * The shared sort instance.
    */
   public static final TypeKeywordSort INSTANCE = new TypeKeywordSort();

   /**
    * No other instances.
    */
   private TypeKeywordSort() {
      super("Type");
   }

}
