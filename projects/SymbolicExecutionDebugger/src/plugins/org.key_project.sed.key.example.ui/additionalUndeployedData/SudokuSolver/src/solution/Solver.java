package solution;

import game.Field;
import game.Sudoku;
import rule.BlockRule;
import rule.HorizontalLineRule;
import rule.IRule;
import rule.VerticalLineRule;
import solution.exception.InvalidSudokuException;

public class Solver extends AbstractSolver {
   private final IRule[] testers;

   private final Sudoku sudoku;

   public Solver(Sudoku sudoku) {
      this(sudoku, getDefaultTester());
   }

   public Solver(Sudoku sudoku, IRule[] testers) {
      this.sudoku = sudoku;
      this.testers = testers;
      if (!isValid()) {
         throw new InvalidSudokuException("Initial Sudoku is not valid.");
      }
   }

   public static IRule[] getDefaultTester() {
      return new IRule[] { new HorizontalLineRule(), new VerticalLineRule(),
            new BlockRule() };
   }

   protected boolean removeInvalidValues() {
      boolean globalChanged = false;
      Field[] goals = sudoku.getGoals();
      if (goals.length >= 1) {
         boolean somethingChanged;
         do {
            somethingChanged = false;
            for (Field goal : goals) {
               if (checkPossibleNumbers(goal)) {
                  somethingChanged = true;
                  globalChanged = true;
               }
            }
            goals = sudoku.getGoals();
         }
         while (somethingChanged);
      }
      return globalChanged;
   }

   /*@ requires \inv;
     @ requires goal != null && goal.\inv && goal.possibleValues != null;
     @ requires goal.possibleValues.array != null;
     @ ensures true;
     @*/
   private boolean checkPossibleNumbers(Field goal) {
      // Remove invalid values
      Object[] possibleValues = goal.getPossibleValues();
      /*@ loop_invariant \index >= 0 && \index <= possibleValues.length;
        @ decreasing possibleValues.length - \index;
        @*/      
      for (Object possibleValue : possibleValues) {
         if (isInvalid(goal, possibleValue)) {
            goal.removePossibleValue(possibleValue);
         }
      }
      // Check if only one value remains, if so set it.
      Object[] remainingPossibleValues = goal.getPossibleValues();
      if (remainingPossibleValues.length == 1) {
         if (isInvalid(goal, remainingPossibleValues[0])) {
            throw new InvalidSudokuException("Invalid solution detected.");
         }
         goal.setValue(remainingPossibleValues[0]);
         return true;
      }
      else {
         return false;
      }
   }
   
   
private boolean initia = true;
   
   protected boolean guessValue() {
      Sudoku clone = sudoku.clone();
      Field goal = clone.getFirstGoal();
      Object[] goalValues = goal.getPossibleValues();
      int i = 0;
      goal.setValue(goalValues[i]);
      /*@ loop_invariant i >= 0 && i <= goalValues.length;
        @ decreasing goalValues.length - i;
        @*/
      while (!isSolved() && i < goalValues.length) {
         try {
            Solver cloneSolver = new Solver(clone, testers);
            cloneSolver.solve();
            // Clone is solved, copy its solution back to the original sudoku
            Field[] targetGoals = sudoku.getGoals();
            for (Field targetGoal : targetGoals) {
               targetGoal.setValue(clone.getValue(targetGoal.getRow(),
                     targetGoal.getColumn()));
            }
         }
         catch (InvalidSudokuException e) {
            // Nothing to do, try another value in next loop iteration.
         }
         finally {
            i++;
         }
      }
      if (!isSolved()) {
         throw new InvalidSudokuException("No valid solution found.");
      }
      return false;
   }

//   private void printJML(PrintStream out) {
//      out.println();
//      out.println();
//      out.println();
//      out.println();
//      
//      if (testers != null) {
//         out.println("testers != null &&");
//         out.println("testers.length == " + testers.length + " &&");
//         for (int i = 0; i < testers.length; i++) {
//            out.println("testers[" + i + "] instanceof " + testers[i].getClass().getName() + " &&");
//         }
//      }
//      else {
//         out.println("testers == null &&");
//      }
//      
//      if (sudoku != null) {
//         out.println("sudoku != null &&");
////         printJMLFields(out, "sudoku.blocks", sudoku.blocks);
//         printJMLFields(out, "sudoku.fields", sudoku.fields);
//      }
//      else {
//         out.println("sudoku == null &&");
//      }
//   }
//
//   private void printJMLFields(PrintStream out, String prefix, Field[][] fields) {
//      if (fields != null) {
//         out.println(prefix + " != null &&");
//         out.println(prefix + ".length == " + fields.length + " &&");
//         for (int i = 0; i < fields.length; i++) {
//            if (fields[i] != null) {
//               out.println(prefix + "[" + i + "] != null &&");
//               out.println(prefix + "[" + i + "].length == " + fields[i].length + " &&");
//               for (int j = 0; j < fields[i].length; j++) {
//                  if (fields[i] != null) {
//                     out.println(prefix + "[" + i + "][" + j + "] != null &&");
//                     printJMLField(out, prefix + "[" + i + "][" + j + "]", fields[i][j]);
//                  }
//                  else {
//                     out.println(prefix + "[" + i + "][" + j + "] == null &&");
//                  }
//               }
//            }
//            else {
//               out.println(prefix + "[" + i + "] == null &&");
//            }
//         }
//      }
//      else {
//         out.println(prefix + " == null &&");
//      }
//   }
//
//   private void printJMLField(PrintStream out, String prefix, Field field) {
//      if (field != null) {
//         out.println(prefix + " != null &&");
//         out.println(prefix + ".block == " + field.block + " &&");
//         out.println(prefix + ".column == " + field.column + " &&");
//         out.println(prefix + ".indexInBlock == " + field.indexInBlock + " &&");
//         out.println(prefix + ".row == " + field.row + " &&");
//         printJMLObjectList(out, prefix + ".possibleValues", field.possibleValues);
//         out.println(prefix + ".sudoku == sudoku &&");
//         if (field.value != null) {
//            out.println(prefix + ".value instanceof " + field.value.getClass().getName() + " &&");
//            out.println("((" + field.value.getClass().getName() + ")" + prefix + ".value).value == " + field.value + " &&");
//         }
//         else {
//            out.println(prefix + ".value == null &&");
//         }
//      }
//      else {
//         out.println(prefix + " == null &&");
//      }
//   }
//
//   private void printJMLObjectList(PrintStream out, String prefix, ObjectList list) {
//      if (list != null) {
//         out.println(prefix + " != null &&");
//         if (list.array != null) {
//            out.println(prefix + ".array != null &&");
//            out.println(prefix + ".array.length == " + list.array.length + " &&");
//            for (int i = 0; i < list.array.length; i++) {
//               out.println(prefix + ".array[" + i + "] instanceof " + list.array[i].getClass().getName() + " &&");
//               out.println("((" + list.array[i].getClass().getName() + ")" + prefix + ".array[" + i + "]).value == " + list.array[i] + " &&");
//            }
//         }
//         else {
//            out.println(prefix + ".array == null &&");
//         }
//      }
//      else {
//         out.println(prefix + " == null &&");
//      }
//   }

   protected boolean guessValueWorks() {
      Field goal = sudoku.getFirstGoal();
      Object[] goalValues = goal.getPossibleValues();
      int i = 0;
      while (!isSolved() && i < goalValues.length) {
         try {
            Sudoku clone = sudoku.clone();
            clone.setValue(goal.getRow(), goal.getColumn(), goalValues[i]);
            Solver cloneSolver = new Solver(clone, testers);
            cloneSolver.solve();
            // Clone is solved, copy its solution back to the original sudoku
            Field[] targetGoals = sudoku.getGoals();
            for (Field targetGoal : targetGoals) {
               targetGoal.setValue(clone.getValue(targetGoal.getRow(),
                     targetGoal.getColumn()));
            }
         }
         catch (InvalidSudokuException e) {
            // Nothing to do, try another value in next loop iteration.
         }
         finally {
            i++;
         }
      }
      if (!isSolved()) {
         throw new InvalidSudokuException("No valid solution found.");
      }
      return false;
   }

   /*@ normal_behavior
     @ requires true;
     @ ensures true;
     @*/
   protected/* @ pure @ */boolean isInvalid(Field goal, Object possibleValue) {
      boolean invalid = false;
      int index = 0;
      while (!invalid && index < testers.length) {
         if (testers[index].isInvalid(goal, possibleValue)) {
            invalid = true;
         }
         index++;
      }
      return invalid;
   }

   /*@ normal_behavior
     @ requires true;
     @ ensures true;
     @*/
   public/* @ pure @ */boolean isValid() {
      boolean valid = true;
      int i = 0;
      while (valid && i < testers.length) {
         valid = testers[i].testValidity(sudoku);
         i++;
      }
      return valid;
   }

   /*@ normal_behavior
     @ requires true;
     @ ensures true;
     @*/
   public/* @ pure @ */boolean isSolved() {
      boolean solved = true;
      int i = 0;
      while (solved && i < testers.length) {
         solved = testers[i].testSolution(sudoku);
         i++;
      }
      return solved;
   }
}
