package myPackage;

public class MyClass {
   /*@ normal_behavior
     @ ensures true;
     @*/
   public MyClass() {
   }
   
   public static int magic() {
      return 42;
   }
}
