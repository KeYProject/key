
public class VerifyMin {
   /*@ normal_behavior
     @ ensures x < y ==> \result == x;
     @ ensures x >= y ==> \result == y;
     @ assignable \strictly_nothing;
     @*/
   public static int min(int x, int y) {
      if (x < y) {
         return x;
      }
      else {
         return y;
      }
   }
}
