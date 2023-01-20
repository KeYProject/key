public class LabelLost {
   /*@ normal_behavior
     @ requires q;
     @ requires p;
     @ ensures p | q & p;
     @*/
   public static void magic(boolean p, boolean q) {
   }
}
