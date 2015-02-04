
public class ValueChange {
   private int value;
   
   public static ValueChange a;
   
   public static ValueChange b;
   
   /*@ normal_behavior
     @ requires a != b;
     @ requires \invariant_for(a);
     @ requires \invariant_for(b);
     @ ensures \result == -4711;
     @ assignable \everything;
     @*/
   public static int main() {
      a.value = 47;
      b.value = -4711;
      int resultValue = zero() + a.value;
      return resultValue;
   }

   private static int zero() {
      a = b;
      return 0;
   }
}
