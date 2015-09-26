package test;

import destPackage.*;

public class TestClass {
   
   /*@
     @ normal_behavior
     @ ensures \result == SourceClass.someField;
     @*/
   public int getSomeField() {
      return SourceClass.someField;
   }
   
   /*@
     @ normal_behavior
     @ ensures \result == Dest.fieldToMove;
     @*/
   public int getFieldToMove() {
      return Dest.fieldToMove;
   }
}