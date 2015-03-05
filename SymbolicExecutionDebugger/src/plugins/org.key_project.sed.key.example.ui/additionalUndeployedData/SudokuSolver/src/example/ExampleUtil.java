package example;

import util.IntWrapper;
import game.Sudoku;

public final class ExampleUtil {
   private ExampleUtil() {
   }
   
//   public static MultiSudoku createExample5() {
//      MultiSudoku multiSudoku = new MultiSudoku(2, 
//                                                new OverlapInfo(0, 8, 1, 0));
//
//      multiSudoku.setValue(0, 0, 3, 8);
//      multiSudoku.setValue(0, 0, 5, 5);
//
//      multiSudoku.setValue(0, 1, 2, 5);
//      multiSudoku.setValue(0, 1, 3, 9);
//      multiSudoku.setValue(0, 1, 5, 3);
//      multiSudoku.setValue(0, 1, 6, 6);
//      
//      multiSudoku.setValue(0, 2, 1, 4);
//      multiSudoku.setValue(0, 2, 7, 9);
//
//      multiSudoku.setValue(0, 3, 0, 9);
//      multiSudoku.setValue(0, 3, 1, 5);
//      multiSudoku.setValue(0, 3, 7, 8);
//      multiSudoku.setValue(0, 3, 8, 4);
//
//      multiSudoku.setValue(0, 5, 0, 3);
//      multiSudoku.setValue(0, 5, 1, 7);
//      multiSudoku.setValue(0, 5, 7, 2);
//      multiSudoku.setValue(0, 5, 8, 1);
//
//      multiSudoku.setValue(0, 6, 1, 6);
//
//      multiSudoku.setValue(0, 7, 2, 1);
//      multiSudoku.setValue(0, 7, 3, 6);
//      multiSudoku.setValue(0, 7, 5, 4);
//
//      multiSudoku.setValue(0, 8, 3, 3);
//      multiSudoku.setValue(0, 8, 5, 7);
//
//      multiSudoku.setValue(1, 0, 3, 9);
//      multiSudoku.setValue(1, 0, 5, 6);
//
//      multiSudoku.setValue(1, 1, 3, 7);
//      multiSudoku.setValue(1, 1, 5, 3);
//      multiSudoku.setValue(1, 1, 6, 9);
//
//      multiSudoku.setValue(1, 2, 7, 5);
//
//      multiSudoku.setValue(1, 3, 0, 5);
//      multiSudoku.setValue(1, 3, 1, 8);
//      multiSudoku.setValue(1, 3, 7, 4);
//      multiSudoku.setValue(1, 3, 8, 2);
//
//      multiSudoku.setValue(1, 5, 0, 3);
//      multiSudoku.setValue(1, 5, 1, 4);
//      multiSudoku.setValue(1, 5, 7, 8);
//      multiSudoku.setValue(1, 5, 8, 9);
//
//      multiSudoku.setValue(1, 6, 1, 3);
//      multiSudoku.setValue(1, 6, 7, 2);
//
//      multiSudoku.setValue(1, 7, 2, 6);
//      multiSudoku.setValue(1, 7, 3, 2);
//      multiSudoku.setValue(1, 7, 5, 4);
//      multiSudoku.setValue(1, 7, 6, 7);
//
//      multiSudoku.setValue(1, 8, 3, 3);
//      multiSudoku.setValue(1, 8, 5, 1);
//      
//      return multiSudoku;
//   }
//   
//   public static MultiSudoku createExample4() {
//      MultiSudoku multiSudoku = new MultiSudoku(2, 
//                                                new OverlapInfo(0, 4, 1, 0),
//                                                new OverlapInfo(0, 5, 1, 1),
//                                                new OverlapInfo(0, 7, 1, 3),
//                                                new OverlapInfo(0, 8, 1, 4));
//      
//      multiSudoku.setValue(0, 0, 1, 8);
//      multiSudoku.setValue(0, 0, 2, 7);
//
//      multiSudoku.setValue(0, 1, 0, 3);
//      multiSudoku.setValue(0, 1, 4, 2);
//      multiSudoku.setValue(0, 1, 5, 8);
//      multiSudoku.setValue(0, 1, 7, 5);
//
//      multiSudoku.setValue(0, 2, 0, 2);
//
//      multiSudoku.setValue(0, 3, 4, 6);
//
//      multiSudoku.setValue(0, 4, 1, 9);
//      multiSudoku.setValue(0, 4, 3, 8);
//      multiSudoku.setValue(0, 4, 5, 4);
//      multiSudoku.setValue(0, 4, 6, 5);
//
//      multiSudoku.setValue(0, 5, 1, 5);
//      multiSudoku.setValue(0, 5, 4, 3);
//      multiSudoku.setValue(0, 5, 7, 2);
//
//      multiSudoku.setValue(0, 6, 4, 4);
//      multiSudoku.setValue(0, 6, 7, 7);
//
//      multiSudoku.setValue(0, 7, 1, 4);
//      multiSudoku.setValue(0, 7, 5, 6);
//      multiSudoku.setValue(0, 7, 6, 8);
//      multiSudoku.setValue(0, 7, 8, 2);
//
//      multiSudoku.setValue(0, 8, 7, 1);
//
//      multiSudoku.setValue(1, 1, 7, 2);
//
//      multiSudoku.setValue(1, 3, 7, 8);
//
//      multiSudoku.setValue(1, 4, 7, 5);
//
//      multiSudoku.setValue(1, 6, 8, 2);
//
//      multiSudoku.setValue(1, 7, 1, 7);
//      multiSudoku.setValue(1, 7, 3, 2);
//      multiSudoku.setValue(1, 7, 4, 4);
//      multiSudoku.setValue(1, 7, 8, 9);
//
//      multiSudoku.setValue(1, 8, 6, 8);
//      multiSudoku.setValue(1, 8, 7, 3);
//
//      return multiSudoku;
//   }
//   
//   public static MultiSudoku createExample3() {
//      MultiSudoku multiSudoku = new MultiSudoku(2, 
//                                                new OverlapInfo(0, 4, 1, 0),
//                                                new OverlapInfo(0, 5, 1, 1),
//                                                new OverlapInfo(0, 7, 1, 3),
//                                                new OverlapInfo(0, 8, 1, 4));
//      
//      multiSudoku.setValue(0, 0, 1, 2);
//      multiSudoku.setValue(0, 0, 6, 4);
//      multiSudoku.setValue(0, 0, 7, 3);
//
//      multiSudoku.setValue(0, 1, 0, 9);
//      multiSudoku.setValue(0, 1, 2, 3);
//      multiSudoku.setValue(0, 1, 8, 2);
//
//      multiSudoku.setValue(0, 2, 1, 4);
//      multiSudoku.setValue(0, 2, 3, 7);
//      multiSudoku.setValue(0, 2, 8, 5);
//
//      multiSudoku.setValue(0, 3, 2, 2);
//      multiSudoku.setValue(0, 3, 4, 7);
//
//      multiSudoku.setValue(0, 4, 3, 1);
//      multiSudoku.setValue(0, 4, 5, 5);
//
//      multiSudoku.setValue(0, 5, 4, 2);
//
//      multiSudoku.setValue(0, 6, 0, 4);
//      multiSudoku.setValue(0, 6, 7, 8);
//
//      multiSudoku.setValue(0, 7, 0, 8);
//      multiSudoku.setValue(0, 7, 6, 9);
//      multiSudoku.setValue(0, 7, 8, 4);
//
//      multiSudoku.setValue(0, 8, 1, 6);
//      multiSudoku.setValue(0, 8, 2, 7);
//      multiSudoku.setValue(0, 8, 7, 1);
//
//      multiSudoku.setValue(1, 0, 6, 6);
//      multiSudoku.setValue(1, 0, 7, 9);
//
//      multiSudoku.setValue(1, 1, 8, 3);
//
//      multiSudoku.setValue(1, 2, 8, 8);
//
//      multiSudoku.setValue(1, 5, 6, 2);
//
//      multiSudoku.setValue(1, 6, 0, 5);
//      multiSudoku.setValue(1, 6, 5, 8);
//      multiSudoku.setValue(1, 6, 7, 7);
//
//      multiSudoku.setValue(1, 7, 0, 4);
//      multiSudoku.setValue(1, 7, 6, 5);
//      multiSudoku.setValue(1, 7, 8, 1);
//
//      multiSudoku.setValue(1, 8, 1, 6);
//      multiSudoku.setValue(1, 8, 2, 1);
//      multiSudoku.setValue(1, 8, 7, 2);
//
//      return multiSudoku;
//   }
//   
//   public static MultiSudoku createExample2() {
//      MultiSudoku multiSudoku = new MultiSudoku(2, 
//                                                new OverlapInfo(0, 7, 1, 0),
//                                                new OverlapInfo(0, 8, 1, 1));
//      
//      multiSudoku.setValue(0, 0, 1, 3);
//      multiSudoku.setValue(0, 0, 4, 2);
//      multiSudoku.setValue(0, 0, 7, 8);
//
//      multiSudoku.setValue(0, 1, 0, 6);
//      multiSudoku.setValue(0, 1, 2, 7);
//      multiSudoku.setValue(0, 1, 6, 5);
//      multiSudoku.setValue(0, 1, 8, 4);
//
//      multiSudoku.setValue(0, 2, 1, 5);
//      multiSudoku.setValue(0, 2, 4, 4);
//      multiSudoku.setValue(0, 2, 7, 1);
//
//      multiSudoku.setValue(0, 3, 3, 3);
//      multiSudoku.setValue(0, 3, 5, 9);
//
//      multiSudoku.setValue(0, 4, 0, 1);
//      multiSudoku.setValue(0, 4, 2, 3);
//      multiSudoku.setValue(0, 4, 4, 5);
//      multiSudoku.setValue(0, 4, 6, 8);
//      multiSudoku.setValue(0, 4, 8, 9);
//
//      multiSudoku.setValue(0, 5, 3, 6);
//      multiSudoku.setValue(0, 5, 5, 2);
//
//      multiSudoku.setValue(0, 6, 1, 7);
//
//      multiSudoku.setValue(0, 7, 0, 2);
//      multiSudoku.setValue(0, 7, 2, 9);
//
//      multiSudoku.setValue(0, 8, 1, 8);
//
//      
//      multiSudoku.setValue(1, 0, 7, 3);
//
//      multiSudoku.setValue(1, 1, 6, 4);
//      multiSudoku.setValue(1, 1, 8, 2);
//      
//      multiSudoku.setValue(1, 2, 7, 6);
//
//      multiSudoku.setValue(1, 3, 3, 1);
//      multiSudoku.setValue(1, 3, 5, 4);
//
//      multiSudoku.setValue(1, 4, 0, 6);
//      multiSudoku.setValue(1, 4, 2, 1);
//      multiSudoku.setValue(1, 4, 4, 7);
//      multiSudoku.setValue(1, 4, 6, 8);
//      multiSudoku.setValue(1, 4, 8, 3);
//
//      multiSudoku.setValue(1, 5, 3, 8);
//      multiSudoku.setValue(1, 5, 5, 3);
//
//      multiSudoku.setValue(1, 6, 1, 1);
//      multiSudoku.setValue(1, 6, 4, 3);
//      multiSudoku.setValue(1, 6, 7, 2);
//
//      multiSudoku.setValue(1, 7, 0, 4);
//      multiSudoku.setValue(1, 7, 2, 2);
//      multiSudoku.setValue(1, 7, 6, 7);
//      multiSudoku.setValue(1, 7, 8, 9);
//
//      multiSudoku.setValue(1, 8, 1, 5);
//      multiSudoku.setValue(1, 8, 4, 1);
//      multiSudoku.setValue(1, 8, 7, 8);
//
//      return multiSudoku;
//   }
//
//   public static MultiSudoku createExample1() {
//      MultiSudoku multiSudoku = new MultiSudoku(2, 
//                                                new OverlapInfo(0, 7, 1, 0),
//                                                new OverlapInfo(0, 8, 1, 1));
//      multiSudoku.setValue(0, 0, 2, 4);
//      multiSudoku.setValue(0, 0, 3, 9);
//      multiSudoku.setValue(0, 0, 5, 1);
//      multiSudoku.setValue(0, 0, 6, 8);
//
//      multiSudoku.setValue(0, 1, 1, 3);
//      multiSudoku.setValue(0, 1, 3, 2);
//      multiSudoku.setValue(0, 1, 5, 6);
//      multiSudoku.setValue(0, 1, 7, 7);
//
//      multiSudoku.setValue(0, 2, 0, 2);
//      multiSudoku.setValue(0, 2, 8, 5);
//
//      multiSudoku.setValue(0, 3, 0, 7);
//      multiSudoku.setValue(0, 3, 1, 4);
//      multiSudoku.setValue(0, 3, 7, 5);
//      multiSudoku.setValue(0, 3, 8, 2);
//
//      multiSudoku.setValue(0, 5, 0, 1);
//      multiSudoku.setValue(0, 5, 1, 8);
//      multiSudoku.setValue(0, 5, 7, 6);
//      multiSudoku.setValue(0, 5, 8, 9);
//
//      multiSudoku.setValue(0, 6, 0, 6);
//      multiSudoku.setValue(0, 6, 6, 5);
//      multiSudoku.setValue(0, 6, 8, 7);
//
//      multiSudoku.setValue(0, 7, 1, 2);
//      multiSudoku.setValue(0, 7, 3, 8);
//      multiSudoku.setValue(0, 7, 5, 7);
//      multiSudoku.setValue(0, 7, 6, 4);
//      multiSudoku.setValue(0, 7, 8, 6);
//
//      multiSudoku.setValue(0, 8, 2, 9);
//      multiSudoku.setValue(0, 8, 3, 5);
//      multiSudoku.setValue(0, 8, 5, 3);
//
//      multiSudoku.setValue(1, 0, 6, 8);
//      multiSudoku.setValue(1, 1, 7, 2);
//      multiSudoku.setValue(1, 2, 8, 7);
//
//      multiSudoku.setValue(1, 3, 0, 2);
//      multiSudoku.setValue(1, 3, 1, 7);
//      multiSudoku.setValue(1, 3, 7, 3);
//      multiSudoku.setValue(1, 3, 8, 6);
//      
//      multiSudoku.setValue(1, 5, 0, 9);
//      multiSudoku.setValue(1, 5, 1, 5);
//      multiSudoku.setValue(1, 5, 7, 8);
//      multiSudoku.setValue(1, 5, 8, 2);
//
//      multiSudoku.setValue(1, 6, 0, 3);
//      multiSudoku.setValue(1, 6, 8, 8);
//      
//      multiSudoku.setValue(1, 7, 1, 8);
//      multiSudoku.setValue(1, 7, 3, 6);
//      multiSudoku.setValue(1, 7, 5, 3);
//      multiSudoku.setValue(1, 7, 7, 1);
//
//      multiSudoku.setValue(1, 8, 2, 1);
//      multiSudoku.setValue(1, 8, 3, 9);
//      multiSudoku.setValue(1, 8, 5, 8);
//      multiSudoku.setValue(1, 8, 6, 3);
//
//      return multiSudoku;
//   }
   
   public static Sudoku createExampleB() {
      Sudoku sudoku = new Sudoku();

      sudoku.setValue(0, 6, new IntWrapper(1));
      sudoku.setValue(0, 8, new IntWrapper(3));
      
//      sudoku.setValue(1, 0, new IntWrapper(5));
      sudoku.setValue(1, 1, new IntWrapper(3));
//      sudoku.setValue(1, 3, new IntWrapper(4));
      sudoku.setValue(1, 5, new IntWrapper(9));
//      sudoku.setValue(1, 6, new IntWrapper(6));
      sudoku.setValue(1, 7, new IntWrapper(2));

//      sudoku.setValue(2, 0, new IntWrapper(6));
      sudoku.setValue(2, 4, new IntWrapper(5));
      sudoku.setValue(2, 7, new IntWrapper(7));
      
//      sudoku.setValue(3, 2, new IntWrapper(5));
      sudoku.setValue(3, 3, new IntWrapper(6));
      sudoku.setValue(3, 8, new IntWrapper(2));

      sudoku.setValue(4, 4, new IntWrapper(9));

//      sudoku.setValue(5, 0, new IntWrapper(3));
      sudoku.setValue(5, 5, new IntWrapper(5));
      sudoku.setValue(5, 6, new IntWrapper(9));

//      sudoku.setValue(6, 1, new IntWrapper(8));
      sudoku.setValue(6, 2, new IntWrapper(2));
      sudoku.setValue(6, 8, new IntWrapper(5));

      sudoku.setValue(7, 1, new IntWrapper(5));
      sudoku.setValue(7, 2, new IntWrapper(3));
      sudoku.setValue(7, 3, new IntWrapper(1));
//      sudoku.setValue(7, 6, new IntWrapper(7));
      sudoku.setValue(7, 7, new IntWrapper(8));
      sudoku.setValue(7, 8, new IntWrapper(4));

      sudoku.setValue(8, 2, new IntWrapper(6));
      return sudoku;
   }
   
   public static Sudoku createExampleA() {
      Sudoku sudoku = new Sudoku();

      sudoku.setValue(0, 6, new IntWrapper(1));
      sudoku.setValue(0, 8, new IntWrapper(3));
      
      sudoku.setValue(1, 0, new IntWrapper(5));
      sudoku.setValue(1, 1, new IntWrapper(3));
      sudoku.setValue(1, 2, new IntWrapper(7));
      sudoku.setValue(1, 3, new IntWrapper(4));
      sudoku.setValue(1, 5, new IntWrapper(9));
      sudoku.setValue(1, 6, new IntWrapper(6));
      sudoku.setValue(1, 7, new IntWrapper(2));

      sudoku.setValue(2, 0, new IntWrapper(6));
      sudoku.setValue(2, 4, new IntWrapper(5));
      sudoku.setValue(2, 6, new IntWrapper(4));
      sudoku.setValue(2, 7, new IntWrapper(7));
      
      sudoku.setValue(3, 2, new IntWrapper(5));
      sudoku.setValue(3, 3, new IntWrapper(6));
      sudoku.setValue(3, 5, new IntWrapper(4));
      sudoku.setValue(3, 8, new IntWrapper(2));

      sudoku.setValue(4, 4, new IntWrapper(9));

      sudoku.setValue(5, 0, new IntWrapper(3));
      sudoku.setValue(5, 3, new IntWrapper(2));
      sudoku.setValue(5, 5, new IntWrapper(5));
      sudoku.setValue(5, 6, new IntWrapper(9));

      sudoku.setValue(6, 1, new IntWrapper(8));
      sudoku.setValue(6, 2, new IntWrapper(2));
      sudoku.setValue(6, 4, new IntWrapper(4));
      sudoku.setValue(6, 8, new IntWrapper(5));

      sudoku.setValue(7, 1, new IntWrapper(5));
      sudoku.setValue(7, 2, new IntWrapper(3));
      sudoku.setValue(7, 3, new IntWrapper(1));
      sudoku.setValue(7, 5, new IntWrapper(2));
      sudoku.setValue(7, 6, new IntWrapper(7));
      sudoku.setValue(7, 7, new IntWrapper(8));
      sudoku.setValue(7, 8, new IntWrapper(4));

      sudoku.setValue(8, 0, new IntWrapper(4));
      sudoku.setValue(8, 2, new IntWrapper(6));
      return sudoku;
   }
}
