package recursion;

public class A {
   
   //@ public normal_behavior ensures \result == 0;
   public static int a() {
      return 0 + B.b();
   }
}