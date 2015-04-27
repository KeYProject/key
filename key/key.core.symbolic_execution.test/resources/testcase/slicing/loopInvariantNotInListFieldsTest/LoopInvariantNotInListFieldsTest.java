
public class LoopInvariantNotInListFieldsTest {
   private int i;
   
   private int j;
   
   private int k;
   
   public int main() {
      i = 2;
      j = 123;
      k = 0;
      /*@ loop_invariant i >= 0;
        @ decreasing i;
        @ assignable i, j;
        @*/
      while (i > 0) {
         i--;
      }
      return k;
   }
}
