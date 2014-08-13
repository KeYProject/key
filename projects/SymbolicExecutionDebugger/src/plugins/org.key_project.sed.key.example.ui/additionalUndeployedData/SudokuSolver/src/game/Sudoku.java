package game;

import game.event.SudokuEvent;
import game.event.SudokuListener;
import game.event.SudokuListenerList;

import java.io.PrintStream;

import util.IntWrapper;
import util.ObjectList;

public class Sudoku implements Cloneable {
   public final ObjectList possibleValues;

   public final Field[][] fields;
   
   public final Field[][] blocks;
   
   public final FieldList goals = new FieldList();
   
   public final SudokuListenerList listener = new SudokuListenerList();
   
   public Sudoku() {
      this(getNumbersOneToNine(), 3);
   }

   public Sudoku(ObjectList possibleValues, int columnsPerBlock) {
      if (possibleValues == null || possibleValues.isEmpty()) {
         throw new RuntimeException("No possible values defined.");
      }
      this.possibleValues = new ObjectList(possibleValues);
      if (size() % columnsPerBlock != 0) {
         throw new RuntimeException("Num of values " + size() + " is not devidable by columns per block " + columnsPerBlock + ".");
      }
      fields = new Field[size()][size()];
      blocks = new Field[size()][size()];
      int linesPerBlock = size() / columnsPerBlock;
      int blockIdPerColumn = -1;
      int blockIdPerRow = -1;
      for (int row = 0; row < size(); row++) {
         if (row % linesPerBlock == 0) {
            blockIdPerRow++;
         }
         for (int column = 0; column < size(); column++) {
            if (column % columnsPerBlock == 0) {
               blockIdPerColumn++;
            }
            Field field = new Field(this, 
                                    row, 
                                    column, 
                                    (blockIdPerRow * linesPerBlock + blockIdPerColumn), 
                                    (row % linesPerBlock * linesPerBlock) + column % columnsPerBlock, 
                                    possibleValues);
            fields[row][column] = field;
            blocks[field.getBlock()][field.getIndexInBlock()] = field;
            goals.add(field);
         }
         blockIdPerColumn = -1;
      }
   }
   
   private Sudoku(Sudoku parent) {
      this.possibleValues = new ObjectList(parent.possibleValues);
      fields = new Field[size()][size()];
      blocks = new Field[size()][size()];
      for (int row = 0; row < parent.size(); row++) {
         for (int column = 0; column < parent.size(); column++) {
            Field original = parent.fields[row][column];
            Field field;
            if (original.isValueSet()) {
               if (original.getPossibleValues().length != 0) {
                  throw new RuntimeException("Field with value has possible values.");
               }
               field = new Field(this, 
                                 row, 
                                 column, 
                                 original.getBlock(), 
                                 original.getIndexInBlock(), 
                                 original.getValue());
            }
            else {
               Object[] originalPossibleValues = original.getPossibleValues(); 
               ObjectList fieldPossibleValues = new ObjectList();
               for (Object value : originalPossibleValues) {
                  fieldPossibleValues.add(value);
               }
               field = new Field(this, 
                                 row, 
                                 column, 
                                 original.getBlock(), 
                                 original.getIndexInBlock(), 
                                 fieldPossibleValues);
               goals.add(field);
            }
            fields[row][column] = field;
            blocks[field.getBlock()][field.getIndexInBlock()] = field;
         }
      }
   }
   
   /*@ normal_behavior
     @ requires true;
     @ ensures \result != this && \result != null && \result.equals(this);
     @*/
   public /*@ pure @*/ Sudoku clone() {
      return new Sudoku(this);
   }
   
   public Field getField(int row, int column) {
      return fields[row][column];
   }
   
   public Object getValue(int row, int column) {
      return fields[row][column].getValue();
   }

   public boolean isValueSet(int row, int column) {
      return fields[row][column].isValueSet(); 
   }

   public void setValue(int row, int column, Object value) {
      fields[row][column].setValue(value);
   }
   
   public int size() {
      return possibleValues.size();
   }

   public boolean isBlockValueSet(int block, int indexInBlock) {
      return blocks[block][indexInBlock].isValueSet();
   }

   public Object getBlockValue(int block, int indexInBlock) {
      return blocks[block][indexInBlock].getValue();
   }
   
   protected void removeGoal(Field field) {
      goals.remove(field);
   }
   
   /*@ normal_behavior
     @ requires !goals.isEmpty();
     @ ensures \result == goals.get(0);
     @
     @ also
     @ normal_behavior
     @ requires goals.isEmpty();
     @ ensures \result == null;
     @*/
   public /*@ pure @*/ Field getFirstGoal() {
      if (!goals.isEmpty()) {
         return goals.get(0);
      }
      else {
         return null;
      }
   }
   
   public Field[] getGoals() {
      return goals.toArray();
   }
   
   public void addSudokuListener(SudokuListener l) {
      if (l != null) {
         listener.add(l);
      }
   }
   
   public void removeSudokuListener(SudokuListener l) {
      if (l != null) {
         listener.remove(l);
      }
   }
   
   protected void firePossibleValueRemoved(Field field, Object value) {
      for (int i = 0; i < listener.size(); i++) {
         listener.get(i).possibleValueRemoved(new SudokuEvent(this, field, value));
      }
   }
   
   protected void fireValueSet(Field field, Object value) {
      for (int i = 0; i < listener.size(); i++) {
         listener.get(i).valueSet(new SudokuEvent(this, field, value));
      }
   }

   public Field getBlockField(int block, int indexInBlock) {
      return blocks[block][indexInBlock];
   }

   public static ObjectList getNumbersOneToNine() {
      ObjectList result = new ObjectList();
      for (int i = 1; i <= 9; i++) {
         result.add(new IntWrapper(i));
      }
      return result;
   }

   public void print() {
      print(System.out);
   }

   public void print(PrintStream out) {
      out.print(toString());
   }

   public String toString() {
      String result = "";
      for (int row = 0; row < size(); row++) {
         for (int column = 0; column < size(); column++) {
            if (fields[row][column].isValueSet()) {
               result += fields[row][column].getValue();
            }
            else {
               result += "?";
            }
            if (column % 3 == 2) {
               result += " ";
            }
         }
         if (row % 3 == 2) {
            result += '\n';
         }
         result += '\n';
      }
      return result;
   }
}
