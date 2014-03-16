package recursion;

public class B {
   
   //@ public normal_behavior ensures \result == 0;
   public static int b() {
      return 0 + C.c();
   }
}
