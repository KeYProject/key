package test;

public class TestClass extends TestParent {
   
   /*@
     @ normal_behavior
     @ ensures \result == aNewMethodName();
     @*/
   int doSomething() {
      return aNewMethodName();
   }
   
   @Override
   int aNewMethodName() {
      return 5;
   }
}