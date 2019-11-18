
public class SimpleInstanceMethodContractApplication {
   /*@ normal_behavior
     @ requires \invariant_for(o);
     @ ensures \result == 42;
     @ assignable \strictly_nothing;
     @*/
   public static int main(SimpleInstanceMethodContractApplication o) {
      return o.doubleValue(21);
   }
   
   /*@ normal_behavior
     @ requires x >= 0 && (\forall int x; x == 0; true);
     @ ensures \result == x * 2;
     @ assignable \strictly_nothing;
     @*/
   public int doubleValue(int x) {
      return x + x;
   }
}
