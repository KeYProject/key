
public class IfThenElseNotFormulaTest {
   /*@ normal_behavior
     @ ensures \result == (x == y ? x >= 0 : y >= 0);
     @*/
   public static boolean magic(int x, int y) {
      if (x == y) {
         return x >= 0;
      }
      else {
         return y >= 0;
      }
   }
}
