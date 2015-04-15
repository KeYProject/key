package org.key_project.jmlediting.core.test.utilities.sort;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeywordSort;

public class WrongInstanceObjectSort extends AbstractKeywordSort {
   public static final WrongInstanceObjectSort INSTANCE = new WrongInstanceObjectSort() {

   };

   public WrongInstanceObjectSort() {
      super("WrongInstanceType");
   }
}