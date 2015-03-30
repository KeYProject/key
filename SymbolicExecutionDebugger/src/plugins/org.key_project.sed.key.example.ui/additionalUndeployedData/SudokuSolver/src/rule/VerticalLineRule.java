package rule;

import game.Field;
import game.Sudoku;
import util.ObjectList;
import util.ObjectSet;

public class VerticalLineRule implements IRule {
   public boolean testValidity(Sudoku sudoku) {
      boolean valid = true;
      int column = 0;
      while (valid && column < sudoku.size()) {
         ObjectSet foundNumbers = new ObjectSet();
         int row = 0;
         while (valid && row < sudoku.size()) {
            if (sudoku.isValueSet(row, column)) {
               if (!foundNumbers.add(sudoku.getValue(row, column))) {
                  valid = false;
               }
            }
            row++;
         }
         column++;
      }
      return valid;
   }

   public boolean testSolution(Sudoku sudoku) {
      boolean valid = true;
      int column = 0;
      while (valid && column < sudoku.size()) {
         ObjectList foundNumbers = new ObjectList();
         int row = 0;
         while (valid && row < sudoku.size()) {
            if (!sudoku.isValueSet(row, column)) {
               valid = false;
            }
            if (valid && !foundNumbers.add(sudoku.getValue(row, column))) {
               valid = false;
            }
            row++;
         }
         column++;
      }
      return valid;
   }

   public boolean isInvalid(Field goal, Object possibleValue) {
      Sudoku sudoku = goal.getSudoku();
      boolean invalid = false;
      int column = goal.getColumn();
      int row = 0;
      while (!invalid && row < sudoku.size()) {
         if (sudoku.isValueSet(row, column)) {
            if (possibleValue.equals(sudoku.getValue(row, column))) {
               invalid = true;
            }
         }
         row++;
      }
      return invalid;
   }
}
