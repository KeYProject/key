package truthValueEvaluation;

public class And {
   /*@ normal_behavior
     @ ensures (p & q) ==> (q & p);
     @*/
   public static void doNothing(boolean p, boolean q) {
   }
}
