
public class DifferentBranchesTest {
   /*@ normal_behavior
     @ ensures \result == 42;
     @*/
   public static int main(/*@ nullable @*/ int[] a) {
      if (a == null) {
         return 42;
      }
      else {
         a[10] = 2;
         a[20] = 4;
         return a[10] + a[20];
      }
   }
}
