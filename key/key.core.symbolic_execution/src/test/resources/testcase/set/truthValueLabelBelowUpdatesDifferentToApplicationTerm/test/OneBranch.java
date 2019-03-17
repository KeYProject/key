
public class OneBranch {
   /*@ normal_behavior
     @ ensures \result == 42;
     @*/
   public /*@ helper @*/ static int magic() {
      return 42;
   }
}
