package recursion;

public class D {
   
   //@ public normal_behavior ensures \result == 0;
   public static int d() {
      return 0 + E.e();
   }
}
