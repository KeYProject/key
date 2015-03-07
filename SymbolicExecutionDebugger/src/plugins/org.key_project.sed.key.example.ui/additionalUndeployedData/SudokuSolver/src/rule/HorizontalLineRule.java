package rule;

import game.Field;
import game.Sudoku;
import util.ObjectSet;

public class HorizontalLineRule implements IRule {
   public boolean testValidity(Sudoku sudoku) {
      boolean valid = true;
      int row = 0;
      while (valid && row < sudoku.size()) {
         ObjectSet foundNumbers = new ObjectSet();
         int column = 0;
         while (valid && column < sudoku.size()) {
            if (sudoku.isValueSet(row, column)) {
               if (!foundNumbers.add(sudoku.getValue(row, column))) {
                  valid = false;
               }
            }
            column++;
         }
         row++;
      }
      return valid;
   }

   public boolean testSolution(Sudoku sudoku) {
      boolean valid = true;
      int row = 0;
      while (valid && row < sudoku.size()) {
         ObjectSet foundNumbers = new ObjectSet();
         int column = 0;
         while (valid && column < sudoku.size()) {
            if (!sudoku.isValueSet(row, column)) {
               valid = false;
            }
            if (valid && !foundNumbers.add(sudoku.getValue(row, column))) {
               valid = false;
            }
            column++;
         }
         row++;
      }
      return valid;
   }

   public boolean isInvalid(Field goal, Object possibleValue) {
      Sudoku sudoku = goal.getSudoku();
      boolean invalid = false;
      int row = goal.getRow();
      int column = 0;
      while (!invalid && column < sudoku.size()) {
         if (sudoku.isValueSet(row, column)) {
            if (possibleValue.equals(sudoku.getValue(row, column))) {
               invalid = true;
            }
         }
         column++;
      }
      return invalid;
   }
}
