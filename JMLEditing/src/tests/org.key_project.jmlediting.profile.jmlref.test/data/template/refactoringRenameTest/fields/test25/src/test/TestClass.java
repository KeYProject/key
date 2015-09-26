package test;

public class TestClass extends TestParent {

   /*@
     @ normal_behavior
     @ ensures \result == fieldToRename;
     @*/
   int returnAnInt() {
      return fieldToRename;
   }
}
