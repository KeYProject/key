
public class AssumesUserInputTest {
   /*@ normal_behavior
     @ ensures \result == x || \result == y;
     @*/   
   public static int min(int x, int y, int z) {
      if (x < y) {
         return x;
      }
      else {
         return y;
      }
   }
}
