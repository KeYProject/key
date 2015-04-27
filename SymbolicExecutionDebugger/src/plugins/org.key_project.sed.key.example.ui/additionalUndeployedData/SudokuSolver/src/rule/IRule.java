package rule;

import game.Field;
import game.Sudoku;

public interface IRule {
   public boolean testValidity(Sudoku sudoku);
   
   public boolean testSolution(Sudoku sudoku);

   public boolean isInvalid(Field goal, Object possibleValue);
}
