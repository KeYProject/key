
public class SimpleStatiLoopInvariantTest {
   private static int i;
   
   public static int main() {
      i = 2;
      /*@ loop_invariant i >= 0;
        @ decreasing i;
        @ assignable i;
        @*/
      while (i > 0) {
         i--;
      }
      return i;
   }
}
