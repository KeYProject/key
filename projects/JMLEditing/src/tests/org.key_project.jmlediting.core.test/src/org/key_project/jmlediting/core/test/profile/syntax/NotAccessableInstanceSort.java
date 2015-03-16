package org.key_project.jmlediting.core.test.profile.syntax;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeywordSort;

public class NotAccessableInstanceSort extends AbstractKeywordSort {
   protected static final NotAccessableInstanceSort INSTANCE = new NotAccessableInstanceSort();

   public NotAccessableInstanceSort() {
      super("NotAccessableInstance");
   }
}