
public class LoopStatementBlockTest {
   public static int nestedLoop() {
      int[] x = new int[] {2, 2};
      for (int i = 0; i < x.length; i++) {
         while (x[i] > 0) {
            x[i]--;
         }
      }
      return 0;
   }
   
   public static int simpleLoop() {
      int x = 3;
      while (x > 0) {
         x--;
      }
      return x;
   }
}
