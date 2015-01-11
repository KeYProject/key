
public class IfThenElseIntegerTest {
   /*@ normal_behavior
     @ ensures \result == (x == y ? 42 : -4711);
     @*/
   public static int magic(int x, int y) {
      if (x == y) {
         return 42;
      }
      else {
         return -4711;
      }
   }
}
