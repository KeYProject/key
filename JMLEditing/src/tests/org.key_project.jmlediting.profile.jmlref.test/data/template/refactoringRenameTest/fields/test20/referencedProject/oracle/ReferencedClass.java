package test;

public class ReferencedClass {
   public int aNewName;
   
   /*@
     @ normal_behavior
     @ ensures \result = this.aNewName;
     @*/
   public /*@ pure @*/ int getBalance() {
      return this.aNewName;
   }
}