
public class LoopInvariantStarFieldsTest {
   private int i;
   
   private int j;
   
   public int main() {
      i = 2;
      j = 123;
      /*@ loop_invariant i >= 0;
        @ decreasing i;
        @ assignable this.*;
        @*/
      while (i > 0) {
         i--;
      }
      return j;
   }
}
