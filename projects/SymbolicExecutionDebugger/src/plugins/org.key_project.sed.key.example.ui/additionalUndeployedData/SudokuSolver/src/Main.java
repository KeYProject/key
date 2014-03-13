import solution.Solver;
import example.ExampleUtil;
import game.Sudoku;

public class Main {
   public static void main(String[] args) {
//      run(ExampleUtil.createExample5());
//      run(ExampleUtil.createExample4());
//      run(ExampleUtil.createExample3());
//      run(ExampleUtil.createExample2());
//      run(ExampleUtil.createExample1());
      run(ExampleUtil.createExampleB());
//      run(ExampleUtil.createExampleA());
   }

//   public static void run(MultiSudoku multiSudoku) {
//      multiSudoku.print();
//      
//      System.out.println();
//      MultiSolver solver = new MultiSolver(multiSudoku);
//      solver.solve();
//      multiSudoku.print();
//      System.out.println("Valid: " + solver.isValid());
//      System.out.println("Solved: " + solver.isSolved());
//   }

   public static void run(Sudoku sudoku) {
      sudoku.print();
      
      System.out.println();
      Solver solver = new Solver(sudoku);
      solver.solve();
      sudoku.print();
      System.out.println("Valid: " + solver.isValid());
      System.out.println("Solved: " + solver.isSolved());
   }
}
