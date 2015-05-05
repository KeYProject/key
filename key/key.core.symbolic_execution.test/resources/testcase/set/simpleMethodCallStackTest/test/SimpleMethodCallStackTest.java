public class SimpleMethodCallStackTest {
   public static int magic(int x, int y) {
      int tempx = nothing(x);
      return tempx;
   }
   
   public static int nothing(int x) {
      return x;
   }
}
