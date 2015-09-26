package test;

public class TestClass extends TestParent {

   /*@
     @ normal_behavior
     @ ensures \result == aNewName;
     @*/
   int returnAnInt() {
      return aNewName;
   }
}
