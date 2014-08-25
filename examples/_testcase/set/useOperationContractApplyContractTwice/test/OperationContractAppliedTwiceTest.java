
public class OperationContractAppliedTwiceTest {
   public static int doubleMagic() {
      int first = magic();
      int second = magic();
      if (first == 42) {
         return first + second;
      }
      else {
         return 0;
      }
   }
   
   /*@ normal_behavior
     @ ensures \result == 42;
     @*/
   public static /*@ strictly_pure @*/ int magic() {
      return 42;
   }
}
