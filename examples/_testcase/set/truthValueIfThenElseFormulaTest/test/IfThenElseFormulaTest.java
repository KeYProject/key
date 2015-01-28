
public class IfThenElseFormulaTest {
   /*@ normal_behavior
     @ ensures (x == y ? \result == x >= 0 : \result == y >= 0);
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
