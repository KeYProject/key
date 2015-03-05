package game;

import util.ObjectList;

public class Field {
   public final Sudoku sudoku;
   
   public final int row;
   
   public final int column;

   public final int block;
   
   public final int indexInBlock;
   
   public final ObjectList possibleValues;
   
   public Object value;

   public Field(Sudoku sudoku, int row, int column, int block, int indexInBlock, Object value) {
      this(sudoku, row, column, block, indexInBlock, new ObjectList());
      if (value == null) {
         throw new RuntimeException("Null value is not supported.");
      }
      this.value = value;
   }

   public Field(Sudoku sudoku, int row, int column, int block, int indexInBlock, ObjectList possibleValues) {
      this.sudoku = sudoku;
      this.row = row;
      this.column = column;
      this.block = block;
      this.indexInBlock = indexInBlock;
      this.possibleValues = new ObjectList(possibleValues);
   }

   public int getBlock() {
      return block;
   }

   /*@ normal_behavior
     @ requires !(this.value != null || !this.value.equals(value));
     @ ensures this.value == value;
     @ ensures this.possibleValues.array.length == 0;
     @
     @ also
     @
     @ exceptional_behavior
     @ requires this.value != null || !this.value.equals(value);
     @ signals (RuntimeException e) true;
     @ assignable \nothing;
     @*/
   public void setValue(Object value) {
      if (this.value != null && !this.value.equals(value)) {
         throw new RuntimeException("Can't change value from " + this.value + " to " + value + ".");
      }
      if (this.value != null ? !this.value.equals(value) : value != null) {
         if (!possibleValues.contains(value)) {
            throw new RuntimeException("Value " + value + " is not possible (" + possibleValues + ").");
         }
         this.value = value;
         this.possibleValues.clear();
         this.sudoku.removeGoal(this);
         this.sudoku.fireValueSet(this, value);
      }
   }

   public Sudoku getSudoku() {
      return sudoku;
   }

   public int getRow() {
      return row;
   }

   public int getColumn() {
      return column;
   }

   public Object getValue() {
      return value;
   }

   /*@ normal_behavior
     @ ensures \result == possibleValues.array;
     @*/
   public Object[] getPossibleValues() {
      return possibleValues.toArray();
   }

   public boolean isValueSet() {
      return value != null;
   }

   public void removePossibleValue(Object invalidValue) {
      if (possibleValues.remove(invalidValue)) {
         sudoku.firePossibleValueRemoved(this, invalidValue);
      }
   }
   
   public int getIndexInBlock() {
      return indexInBlock;
   }

   public String toString() {
      return "Field " + row + ", " + column + " (" + block + ", " + indexInBlock + ") is " + value + " (possible are " + possibleValues + ")";
   }
}
