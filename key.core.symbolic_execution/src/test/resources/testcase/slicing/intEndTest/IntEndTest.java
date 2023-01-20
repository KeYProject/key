
public class IntEndTest {
   /*@ normal_behavior
     @ ensures \result == 42;
     @ assignable \strictly_nothing;
     @*/
   public static int main(int x) {
      x = -4700;
      x = x - 11;
      x = 40;
      x = x + 2;
      return x;
   }
}
