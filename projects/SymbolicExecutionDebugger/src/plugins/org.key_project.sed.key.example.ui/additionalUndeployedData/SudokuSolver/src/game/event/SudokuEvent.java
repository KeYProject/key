package game.event;

import game.Field;
import game.Sudoku;

public class SudokuEvent {
   private final Sudoku source;
	
   private final Field field;
   
   private final Object value;
   
   public SudokuEvent(Sudoku source, Field field, Object value) {
	  this.source = source;
      this.field = field;
      this.value = value;
   }

   public Sudoku getSource() {
      return source;
   }

   public Object getValue() {
      return value;
   }

   public Field getField() {
      return field;
   }
}
