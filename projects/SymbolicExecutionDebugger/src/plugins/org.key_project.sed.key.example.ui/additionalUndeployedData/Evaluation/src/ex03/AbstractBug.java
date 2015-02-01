package ex03;

public abstract class AbstractBug {
   /*@ normal_behavior
     @ ensures \result == 42;
     @*/
   public /*@ pure @*/ int magic() {
      return 666;
   }
}
