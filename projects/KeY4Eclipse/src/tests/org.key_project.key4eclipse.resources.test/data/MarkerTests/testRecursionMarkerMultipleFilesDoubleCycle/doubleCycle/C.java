package recursion;

public class C {
   
   //@ public normal_behavior ensures \result == 0;
   public static int c() {
      return 0+A.a()+D.d();
   }
}
