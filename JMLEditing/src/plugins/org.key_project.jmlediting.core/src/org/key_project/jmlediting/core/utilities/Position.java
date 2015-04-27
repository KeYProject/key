package org.key_project.jmlediting.core.utilities;

/**
 * Class Representing a Position in a Document by ints line and column.
 *
 * @author David Giessing
 *
 */
public class Position {
   /**
    * The line.
    */
   private final int line;
   /**
    * The column.
    */
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

   /**
    * Creates a new Position.
    *
    * @param line
    *           the line
    * @param column
    *           the column
    */
   public Position(final int line, final int column) {
      super();
      this.line = line;
      this.column = column;
   }

}