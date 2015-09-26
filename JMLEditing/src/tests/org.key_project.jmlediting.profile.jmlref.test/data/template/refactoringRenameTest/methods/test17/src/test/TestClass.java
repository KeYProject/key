package test;

public class TestClass extends TestParent {
   
   /*@
     @ normal_behavior
     @ ensures \result == returnAnInteger();
     @*/
   int doSomething() {
      return returnAnInteger();
   }
   
   @Override
   int returnAnInteger() {
      return 5;
   }
}