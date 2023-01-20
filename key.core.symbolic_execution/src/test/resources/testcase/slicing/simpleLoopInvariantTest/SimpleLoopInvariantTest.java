
public class SimpleLoopInvariantTest {
   public static int main() {
      int i = 2;
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
