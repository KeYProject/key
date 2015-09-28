package test;

public class TestClass extends TestParent {
   
   /*@
     @ normal_behavior
     @ ensures \result == ((TestParent) returnParentAsObject).returnAnInteger();
     @*/
   int doSomething() {
      return ((TestParent) returnParentAsObject()).returnAnInteger();
   }
   
   Object returnParentAsObject() {
      return new TestParent();
   }
   

}