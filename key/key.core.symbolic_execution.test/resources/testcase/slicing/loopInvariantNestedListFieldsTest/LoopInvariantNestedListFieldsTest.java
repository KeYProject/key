
public class LoopInvariantNestedListFieldsTest {
   private IntWrapper i;
   
   private IntWrapper j;
   
   private IntWrapper k;
   
   /*@ normal_behavior
     @ requires \invariant_for(obj);
     @ requires obj.i != obj.j;
     @ requires obj.i != obj.k;
     @ requires obj.j != obj.k;
     @ ensures true;
     @*/
   public static int main(LoopInvariantNestedListFieldsTest obj) {
      obj.i.value = 2;
      obj.j.value = 123;
      obj.k.value = 0;
      /*@ loop_invariant obj.i.value >= 0;
        @ decreasing obj.i.value;
        @ assignable obj.i.value;
        @*/
      while (obj.i.value > 0) {
         obj.i.value--;
      }
      return obj.i.value;
   }
   
   private static class IntWrapper {
      private /*@ spec_public @*/ int value;
   }
}
