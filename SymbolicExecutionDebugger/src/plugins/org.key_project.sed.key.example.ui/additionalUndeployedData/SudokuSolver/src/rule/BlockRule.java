package rule;

import game.Field;
import game.Sudoku;
import util.ObjectSet;

public class BlockRule implements IRule {
   public boolean testValidity(Sudoku sudoku) {
      boolean valid = true;
      int block = 0;
      while (valid && block < sudoku.size()) {
         ObjectSet foundNumbers = new ObjectSet();
         int index = 0;
         while (valid && index < sudoku.size()) {
            if (sudoku.isBlockValueSet(block, index)) {
               if (!foundNumbers.add(sudoku.getBlockValue(block, index))) {
                  valid = false;
               }
            }
            index++;
         }
         block++;
      }
      return valid;
   }

   public boolean testSolution(Sudoku sudoku) {
      boolean valid = true;
      int block = 0;
      while (valid && block < sudoku.size()) {
         ObjectSet foundNumbers = new ObjectSet();
         int index = 0;
         while (valid && index < sudoku.size()) {
            if (!sudoku.isBlockValueSet(block, index)) {
               valid = false;
            }
            if (valid && !foundNumbers.add(sudoku.getBlockValue(block, index))) {
               valid = false;
            }
            index++;
         }
         block++;
      }
      return valid;
   }

   public boolean isInvalid(Field goal, Object possibleValue) {
      Sudoku sudoku = goal.getSudoku();
      boolean invalid = false;
      int block = goal.getBlock();
      int index = 0;
      while (!invalid && index < sudoku.size()) {
         if (sudoku.isBlockValueSet(block, index)) {
            if (possibleValue.equals(sudoku.getBlockValue(block, index))) {
               invalid = true;
            }
         }
         index++;
      }
      return invalid;
   }
}
