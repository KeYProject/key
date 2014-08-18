package myPackage;

public class MyClass {
   /*@ normal_behavior
     @ ensures \result == 42;
     @*/
   public static int magic() {
      return 42;
   }
}
