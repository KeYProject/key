
public class AllNodeTypesTest {
   private int value;
   
   /*@ normal_behavior
     @ ensures true;
     @*/
   public static int main(/*@ nullable @*/ AllNodeTypesTest obj) {
      obj.value = 1;
      obj.value = doubleValue(1);
      int result = 0;
      /*@ loop_invariant i >= 0 && i <= 1;
        @ decreasing 2 - i;
        @ assignable \strictly_nothing;
        @*/
      for (int i = 0; i == 0; i++) {
         result++;
      }
      result = doubleValue(result);
      for (int i = 0; i == 0; i++) {
         result++;
      }
      return result;
   }
   
   /*@ normal_behavior
     @ requires x >= 0;
     @ ensures \result == x + x;
     @*/
   public static int doubleValue(int x) {
      return x + x;
   }
}
