
public class EquivExample {
   public static boolean a;
   public static boolean b;
   
   /*@ normal_behavior
     @ ensures \result == a <==> b;
     @*/
   public static boolean equivExample() {
      return a == b;
   }
}
