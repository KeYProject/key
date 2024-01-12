public class MethodCallStackTest {
   public static boolean magic(int x, int y) {
      boolean first = positive(x);
      boolean second = positive(y);
      return first && second;
   }
   
   public static boolean positive(int x) {
      if (x >= 0) {
         return true;
      }
      else {
         return false;
      }
   }
}
