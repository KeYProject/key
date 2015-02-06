package org.key_project.jmlediting.core.utilities;

public class Position {
   private final int line;
   private final int column;

   /**
    * @return the line
    */
   public int getLine() {
      return this.line;
   }

   /**
    * @return the column
    */
   public int getColumn() {
      return this.column;
   }

   public Position(final int line, final int column) {
      super();
      this.line = line;
      this.column = column;
   }

}