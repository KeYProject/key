package test;

public class ReferencedClass {
   public int balance;
   
   /*@
     @ normal_behavior
     @ ensures \result = this.balance;
     @*/
   public /*@ pure @*/ int getBalance() {
      return this.balance;
   }
}