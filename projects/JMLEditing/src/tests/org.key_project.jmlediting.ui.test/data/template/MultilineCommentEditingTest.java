package test;

public class MultilineCommentEditingTest {
   
   /*
    * A collections of variable used here.
    */
   
   private int a;
   private int b;
   private int c;
   private String d;
   
   /*@
     @ public normal_behavior
     @   assignable a;
     @   assignable c;
     @*/
   /**
    * Does something wirh abcd.
    */
   public void abcd() {
      
   }
   
   //@ public normal_behavior
   public void dcba() {
      
   }
   
   
}