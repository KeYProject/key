
public class SimpleMethodContractApplication {
   /*@ normal_behavior
     @ ensures \result == 42;
     @ assignable \strictly_nothing;
     @*/
   public static int main() {
      return doubleValue(21);
   }
   
   /*@ normal_behavior
     @ requires x >= 0 && (\forall int x; x == 0; true);
     @ ensures \result == x * 2;
     @ assignable \strictly_nothing;
     @*/
   public static int doubleValue(int x) {
      return x + x;
   }
}
