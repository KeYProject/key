
public class MethodCallTest {
   private int value;
   
   /*@ normal_behavior
     @ requires \invariant_for(obj);
     @ ensures \result == 4;
     @ assignable \everything;
     @*/
   public static int main(MethodCallTest obj) {
      obj.value = 0;
      sub(obj);
      sub(obj);
      return obj.value;
   }

   public static void sub(MethodCallTest obj) {
      subsub(obj);
   }

   public static void subsub(MethodCallTest obj) {
      obj.value += 2;
   }
}
