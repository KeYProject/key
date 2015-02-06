package org.key_project.jmlediting.ui.test.completion;

public class VectorTest {
   
   protected Cons<Vector2> vectors1;
   protected Cons<Vector2> vectors2;
   protected Cons<Vector2> results;
   
   private Cons<Vector2> intermediateVectors;
   private Vector2 intermediateVector;
   
   public final Object finalTemp = new Object();

   private class Temps {

      private Vector2 temp1;
      private Vector2 temp2;
      protected Vector2 temp3;
      public Cons<Vector2> moreTemps;
      
   }
   
   private Temps temp;
   
   private final Integer secret = 0;
   
   
   /*@
     @ assignable [[1]]
     @*/
   public void doCalculation1() {
      
   }
   
   /*@
     @ assignable vec[[2]];
     @*/
   public void doCalculation2(final boolean vectorParameter) {
      
   }
   
   /*@
     @ public normal_behavior
     @      ensures true;
     @      assignable  temp.[[3]];
     @      requires \not_specified;
     @*/
   public void testProposalsInOtherKeywords() {
      
   }
   
   /*@
     @ assignable [[4]];
     @ assignable vectors2.next.[[5]];
     @ assignable factor.[[6]];
     @ assignable secret.[[7]];
     @*/
   public void doCalculation4_5(double factor, Vector2 newVector) {
      
   }
   
   /*@
     @ assignable secret;[[8]]
     @*/
   public void testNoStoreRefProposalsAfterSemicolon() {
      
   }
   
   /*@
     @ accessible temp.moreTemps.[[9]]
     @*/
   public void testProposalsAfterDotWithoutSemicolo() {
      
   }
   
   /*@
     @ assignable [[10]];
     @ accessible [[11]];
     @*/
   public void testFinal(final boolean doSomething) {
    
   }
   

}
