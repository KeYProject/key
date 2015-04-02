package org.key_project.jmlediting.core.test.profile.syntax;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeywordSort;

public class WrongInstanceObjectSort extends AbstractKeywordSort {
   public static final WrongInstanceObjectSort INSTANCE = new WrongInstanceObjectSort() {

   };

   public WrongInstanceObjectSort() {
      super("WrongInstanceType");
   }
}