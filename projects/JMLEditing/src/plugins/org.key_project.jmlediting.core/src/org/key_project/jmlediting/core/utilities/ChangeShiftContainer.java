package org.key_project.jmlediting.core.utilities;

import org.eclipse.ltk.core.refactoring.Change;

public class ChangeShiftContainer {

   private final Change c;
   private final int shift;

   public ChangeShiftContainer(final Change c, final int shift) {
      this.c = c;
      this.shift = shift;
   }

   public Change getChange() {
      return this.c;
   }

   public int getShift() {
      return this.shift;
   }
}
