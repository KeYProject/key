package org.key_project.jmlediting.core.test.utilities.sort;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeywordSort;

public class NotAccessableInstanceSort extends AbstractKeywordSort {
   protected static final NotAccessableInstanceSort INSTANCE = new NotAccessableInstanceSort();

   public NotAccessableInstanceSort() {
      super("NotAccessableInstance");
   }
}