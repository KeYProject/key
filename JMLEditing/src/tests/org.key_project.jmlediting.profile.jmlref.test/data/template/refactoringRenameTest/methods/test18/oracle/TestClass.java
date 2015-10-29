package test;

public class TestClass extends TestParent {
   
   /*@
     @ normal_behavior
     @ ensures \result == ((TestParent) returnParentAsObject).newMethodName();
     @*/
   int doSomething() {
      return ((TestParent) returnParentAsObject()).newMethodName();
   }
   
   Object returnParentAsObject() {
      return new TestParent();
   }
   

}