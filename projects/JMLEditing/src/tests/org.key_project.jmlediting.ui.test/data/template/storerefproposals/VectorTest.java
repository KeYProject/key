package org.key_project.jmlediting.ui.test.completion;

public class VectorTest {
   
   protected Cons<Vector2> vectors1;
   protected Cons<Vector2> vectors2;
   protected Cons<Vector2> results;
   
   private Cons<Vector2> intermediateVectors;
   private Vector2 intermediateVector;
   
   private class Temps {

      private Vector2 temp1;
      private Vector2 temp2;
      protected Vector2 temp3;
      public Cons<Vector2> moreTemps;
      
   }
   
   private Temps temp;
   
   
   /*@
     @ assignable [[1]]
     @*/
   public void doCalculation1() {
      
   }
   
   /*@
     @ assignable vec[[2]];
     @*/
   public void doCalculation2() {
      
   }
   
   /*@
     @ public normal_behavior
     @      ensures true;
     @      assignable  temp.[[3]];
     @      requires \not_specified;
     @*/
   public void doCalculation3() {
      
   }
   
   /*@
     @ assignable [[4]];
     @ assignable vectors2.cons.[[5]];
     @*/
   public void doCalculation4_5(Double factor) {
      
   }
   

}
