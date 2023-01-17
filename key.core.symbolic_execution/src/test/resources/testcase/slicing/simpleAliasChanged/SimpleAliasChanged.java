
public class SimpleAliasChanged {
   private int value;
   
   /*@ normal_behavior
     @ requires \invariant_for(x);
     @ requires \invariant_for(y);
     @ requires x != y;
     @ ensures \result == 42;
     @ assignable \everything;
     @*/
   public static int main(SimpleAliasChanged x, SimpleAliasChanged y) {
      y.value = 42;
      x.value = -666;
      x = y;
      return x.value;
   }
}
